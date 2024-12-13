import Mathlib

open Classical -- this was needed to use my definition
open Finset


noncomputable section

def complex_nth_hawaiian_circle (n : ℕ):=
  Metric.sphere (1/((n:ℂ)+1)) (1/(((n:ℝ)+1)))

def hawaiian_earring_complex:=
  ⋃ (n:ℕ), complex_nth_hawaiian_circle n


local notation "ℍ" => hawaiian_earring_complex

lemma nth_circle_subset_H (n:ℕ): complex_nth_hawaiian_circle (n : ℕ) ⊆ ℍ:= by
  rw[hawaiian_earring_complex]
  exact Set.subset_iUnion_of_subset n fun ⦃a⦄ a ↦ a

-- Premiliminary results about the fundamental group of the circle



lemma isPathConnected_hawaiian_earring: IsPathConnected hawaiian_earring_complex:= by
  rw[hawaiian_earring_complex]
  unfold complex_nth_hawaiian_circle
  apply isPathConnected_sUnion 0
  simp
  use Metric.sphere 1 1
  use 0
  simp
  simp
  intro n
  have h₁: ((n+1):ℂ) = ((n+1):ℝ):= by
    norm_cast
  rw[h₁]
  rw[Complex.abs_ofReal]
  simp
  norm_cast
  simp

  intro s h
  simp_all
  rcases h with ⟨n,h⟩
  rw[←h]
  apply isPathConnected_sphere
  refine Cardinal.two_le_iff_one_lt.mp ?H3.intro.h.a
  exact le_of_eq (id (Eq.symm (Complex.rank_real_complex)))
  norm_num
  norm_cast
  norm_num

lemma isConnected_hawaiian_earring: IsConnected hawaiian_earring_complex:= by
  apply IsPathConnected.isConnected
  exact isPathConnected_hawaiian_earring

lemma isPreconnected_hawaiian_earring: IsPreconnected hawaiian_earring_complex:= by
  apply IsConnected.isPreconnected
  apply isConnected_hawaiian_earring

lemma zeroth_homotopy_of_hawaiian_earring_trivial: Nonempty (ZerothHomotopy (hawaiian_earring_complex)) ∧ Subsingleton (ZerothHomotopy (hawaiian_earring_complex)):= by
  apply pathConnectedSpace_iff_zerothHomotopy.mp
  refine Iff.mp isPathConnected_iff_pathConnectedSpace ?_
  apply (isPathConnected_hawaiian_earring)

-- Hawaiian earring is closed



-- exercises to help me understand
example(z:ℂ):(∀ ε > 0, Complex.abs (z) ≤ ε) → z = 0:= by
  contrapose
  intro h
  push_neg
  have h': Complex.abs (z) > 0:=by
    exact AbsoluteValue.pos Complex.abs h
  use Complex.abs (z)/2
  constructor
  linarith
  linarith

lemma abs_le_all_nat_eq_zero (z:ℂ):(∀ (n:ℕ), Complex.abs (z) ≤ 1/(n+1)) → z = 0:= by
  contrapose
  intro h
  push_neg
  have h': Complex.abs (z) > 0:=by
    exact AbsoluteValue.pos Complex.abs h
  suffices: ∃ (n:ℕ), 1/ Complex.abs (z) - 1 < n
  rcases this with ⟨m,h''⟩
  use m
  refine (one_div_lt h' ?h.hb).mp ?h.a
  linarith
  exact lt_add_of_tsub_lt_right h''
  use Nat.ceil ( 1/ Complex.abs (z) - 1) + 1
  calc
     1 / Complex.abs z - 1 ≤ (Nat.ceil (1 / Complex.abs z - 1)):= by
      exact Nat.le_ceil (1 / Complex.abs z - 1)
    _< Nat.ceil (1 / Complex.abs z - 1) + 1:= by
      norm_cast
      exact lt_add_one ↑⌈1 / Complex.abs z - 1⌉₊
    _= ↑(⌈1 / Complex.abs z - 1⌉₊ + 1):= by
      norm_cast



lemma closed_ball_inter: ⋂ (n : ℕ), Metric.closedBall (0:ℂ) (1/(n+1)) = {0} := by
  ext z
  constructor
  intro h
  suffices: z=0
  exact this
  refine abs_le_all_nat_eq_zero z ?this.a
  simp at h
  norm_num
  exact fun n ↦ h n

  intro h
  simp_all
  intro n
  norm_cast
  norm_num

#check isClosed_le

-- hideous proof, must be a quicker way!
lemma isClosed_hawaiian_earring: IsClosed ℍ:= by
  --refine { isOpen_compl := ?isOpen_compl }
  have h: ℍ = ⋂ (n:ℕ), (ℍ ∪ Metric.closedBall (0) (1/(n+1))):= by -- helper lemma?
    ext z
    constructor
    intro h
    refine Set.mem_iInter.mpr ?h.mp.a
    intro i
    left
    exact h

    intro h
    by_cases h': ∀n : ℕ, z ∈ Metric.closedBall 0 (1 / (↑n + 1))
    unfold hawaiian_earring_complex
    unfold complex_nth_hawaiian_circle
    refine Set.mem_iUnion.mpr ?_
    use 1
    simp

    suffices: z = (0:ℂ)
    rw[this]
    norm_num
    norm_cast
    have h'': z ∈ ({0}: Set ℂ) ↔ z = 0:= by -- shorten this
      constructor
      intro h
      exact h
      intro h
      exact h
    apply h''.mp
    rw[←closed_ball_inter]
    exact Set.mem_iInter.mpr h'

    push_neg at h'
    rcases h' with ⟨m,h'⟩
    simp_all
    have h'': z ∈ ℍ ∨ Complex.abs z ≤ ((m:ℝ) + 1)⁻¹:= by
      exact h m
    rcases h'' with (l|r)
    exact l
    linarith
  rw[h]
  apply isClosed_iInter
  intro n
                                                          -- this is how to do finite unions
  have h₀:∀(n:ℕ), ℍ ∪ Metric.closedBall 0 (1 / (↑n + 1)) = (⋃ (i: (range (2*n + 1))), complex_nth_hawaiian_circle i) ∪ Metric.closedBall 0 (1 / (↑n + 1)):= by
    intro m
    ext z
    constructor
    rintro (zinH|zinBall)
    unfold hawaiian_earring_complex at zinH
    simp_all
    rcases zinH with ⟨i,b⟩
    simp_all[complex_nth_hawaiian_circle]
    by_cases this: i < 2*m + 1
    left
    use i

    push_neg at this
    right
    calc
      Complex.abs (z) = Complex.abs (z - 1/(i+1) + 1/(i+1)):= by
        simp
      _≤ Complex.abs (z-1/(i+1)) + Complex.abs (1/(i+1)):=by
        exact AbsoluteValue.add_le Complex.abs (z - 1 / (i+1)) (1 / (i+1))
      _= (1/(i+1)) + (1/(i+1)):= by
        norm_num
        rw[b]
        norm_num
        norm_cast
        exact Complex.abs_natCast (i + 1)
      _= 2*(1/(i+1)):= by
        rw[two_mul]

-- this was horrible, easier way?
    have h': ((i:ℝ)+1) ≥ (2*m +2):= by
      norm_cast
      linarith
    have h'': 1/((i:ℝ)+1) ≤ 1/(2*m + 2):= by
      refine one_div_le_one_div_of_le ?ha h'
      linarith
    calc
      2*(1/((i:ℝ)+1)) ≤ 2*(1/(2*m + 2)):= by
        refine mul_le_mul ?h₁ h'' ?c0 ?b0
        rfl
        norm_num
        norm_cast
        norm_num
        norm_num
      _= 2*(1/(2*(m + 1))):= by
        rw [@mul_add_one]
      _= 1/(m + 1):= by
        simp
        norm_num
        rw [@mul_left_comm]
        simp
      _=(↑m + 1)⁻¹:= by
        norm_num

    right
    exact zinBall

    rintro (l|r)
    left

    rw[hawaiian_earring_complex]
    simp
    simp at l
    rcases l with ⟨a,b,c⟩
    use a
    right
    exact r
  rw[h₀]
  apply IsClosed.union
  refine isClosed_iUnion_of_finite ?h.a.h
  intro i
  unfold complex_nth_hawaiian_circle
  exact Metric.isClosed_sphere
  exact Metric.isClosed_ball



lemma isBounded_hawaiian_earring: Bornology.IsBounded ℍ:= by
  rw[hawaiian_earring_complex]
  apply (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mpr -- arg needs to go inside the mp or mpr!
  use 2
  simp
  intro n z h
  rw[complex_nth_hawaiian_circle] at h
  simp_all
  calc
    _=Complex.abs (z - 1/(n+1) + 1/(n+1)):= by
      simp
    _≤ Complex.abs (z - 1/(n+1)) + Complex.abs (1/(n+1)):= by
      exact AbsoluteValue.add_le Complex.abs (z - 1 / (n + 1)) (1 / (n + 1))
    _= 1/(n+1) + 1/(n+1):= by
      norm_num
      rw[h]
      simp
      norm_cast
      exact Complex.abs_natCast (n + 1)
    _= 2*(1/(n+1)):= by
      rw [@two_mul]
    _≤ 2*(1/(0+1)):= by
      simp
      refine inv_le_one ?ha
      norm_cast
      norm_num
  simp


lemma isCompact_hawaiian_earring: IsCompact ℍ:= by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  exact isClosed_hawaiian_earring
  exact isBounded_hawaiian_earring

def my_function (n: ℕ):  ℂ → ℂ:=
  Set.piecewise (complex_nth_hawaiian_circle n) (id) (fun z ↦ 0)

lemma my_retraction_maps_to_circle (n:ℕ): Set.MapsTo (my_function n) (ℍ) (complex_nth_hawaiian_circle n):= by
  rw[Set.MapsTo]
  intro z
  intro h
  rw[my_function] -- could this be turned into a lemma for piecewise functions?/one already?
  by_cases h': z ∈ complex_nth_hawaiian_circle n
  rw[Set.piecewise_eq_of_mem]
  exact h'
  exact h'
  rw[Set.piecewise_eq_of_not_mem]
  rw[complex_nth_hawaiian_circle]
  simp
  norm_cast
  exact Complex.abs_natCast (n + 1)
  exact h'


-- this is how you restrict a map's domain and codomain, do not bother with subtypes explicitly!
def my_function_res (n:ℕ):=
  Set.MapsTo.restrict (my_function n) (ℍ) (complex_nth_hawaiian_circle n) (my_retraction_maps_to_circle n)


-- brackets around the type somehow made the subtype stuff work

-- want to show f is a retraction
example (n:ℕ): CategoryTheory.retraction (my_function n):= by
  sorry

-- want to talk about cty on the Hawaiian earring subspace topology, not in C.
-- MIL: subspace topologies?
-- Have to use subtypes
-- is this using the subspace topology already? Does not seem to be

set_option maxHeartbeats 0 -- needed for the lemmas below

-- these lemmas were used in the cty of the retraction proof
lemma circles_pairwise_intersection (a:ℝ) (b:ℝ) (h: a ≠ b): ∀ (z:ℂ), (Complex.abs (z-a) = a ∧ Complex.abs (z-b) = b) → z = 0:= by
  intro z ⟨l,r⟩
  refine ((fun {z w} ↦ Complex.ext_iff.mpr) ?_)
  simp
  have h₁: z.re = 0:= by



    suffices: ((2*a) - (2*b))*(z.re) = 0
    have h₀: (2*a)-(2*b) ≠ 0:= by
      apply sub_ne_zero_of_ne
      norm_cast
      norm_num
      exact h

    exact (eq_zero_of_ne_zero_of_mul_left_eq_zero h₀ this)


    calc
      _= (z.re)^2  - 2*b*z.re - (z.re)^2 + 2*a*z.re:= by
        simp
        linarith
      _= (z.re - b)^2 - b^2 - (z.re - a)^2 + a^2:= by
        linarith
      _= ((z.re - b)^2  + z.im^2) - b^2 - ((z.re - a)^2 + z.im^2)  + a^2:= by
        linarith
      --_= ((z - b).re)^2 + ((z-b).im)^2 - b^2 - (((z - b).re)^2 + ((z-b).im)^2) +a^2:= by

      _= Complex.abs (z - ↑b)^2 - Complex.abs (z - ↑a)^2 - b^2 + a^2:= by

        simp
        repeat rw [← Complex.normSq_add_mul_I]
        repeat rw [Complex.sq_abs]
        simp
        repeat rw[Complex.normSq_apply]
        simp
        linarith
      _=0:= by
        rw[l,r]
        linarith

  constructor
  exact h₁
  have h₂: (z.re-a)^2 + (z.im)^2 = a^2:= by
    calc
      _=Complex.normSq (↑z.re - ↑a+ ↑z.im * Complex.I):= by
          rw[← Complex.normSq_add_mul_I]
          simp
      _=(Complex.abs (z-a))^2:= by
        rw [Complex.sq_abs]
        repeat rw[Complex.normSq_apply]
        simp
      _= a^2:= by
        rw[l]
  rw[h₁] at h₂
  simp at h₂
  exact h₂

lemma my_open_set_open (n:ℕ): @IsOpen (↑ℍ) instTopologicalSpaceSubtype ({x | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1))\ ({0}:Set ℂ)}):= by
  apply isClosed_compl_iff.mp
  have h₀: {x:ℍ | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1))\ ({0}:Set ℂ)}ᶜ =  ⋂ (k:ℕ), ( {x:ℍ | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1))\ ({0}:Set ℂ)}ᶜ ∪ {z|↑z ∈ Metric.closedBall (0:ℂ) (1 / (k + 1))}):= by
    ext a
    constructor
    intro h
    apply Set.mem_iInter.mpr
    intro i
    left
    exact h

    intro h
    simp
    intro h''
    by_cases h': ∀k : ℕ, a ∈ {z|↑z ∈ Metric.closedBall (0:ℂ) (1 / (k + 1))}
    suffices: (a:ℂ) ∈ ({0}: Set ℂ)
    exact this
    rw[←closed_ball_inter]
    apply Set.mem_iInter.mpr
    simp at h'
    simp
    exact fun i ↦ h' i

    push_neg at h'
    rcases h' with ⟨m,h'⟩
    simp at h'
    simp at h
    rcases h m with (l|r)
    exact l h''
    absurd r
    simp
    exact h'

  rw [h₀]
  apply isClosed_iInter
  intro k

  by_cases h: n ≥ 2*k +1
  suffices: {x :ℍ | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1))\ ({0}:Set ℂ)}ᶜ ∪ {z:ℍ|↑z ∈ Metric.closedBall (0:ℂ) (1 / (k + 1))} = {x:ℍ| ↑x ∈ℍ}
  rw[this]
  simp

  ext a
  constructor
  rintro (l|r)
  simp
  simp

  intro h'
  by_cases this: a ∈ {z | ↑z ∈ Metric.closedBall (0 :ℂ) (1 / (k + 1))}
  right
  exact this
  simp at this
  left
  simp
  intro h''
  absurd this
  simp

  calc
    Complex.abs (a) = Complex.abs (a - 1/(n+1) + 1/(n+1)):= by
      simp
    _≤ Complex.abs (a-1/(n+1)) + Complex.abs (1/(n+1)):=by
      exact AbsoluteValue.add_le Complex.abs (a - 1 / (n+1)) (1 / (n+1))
    _= (1/(n+1)) + (1/(n+1)):= by
      norm_num
      rw[h'']
      norm_num
      norm_cast
      exact Complex.abs_natCast (n + 1)
     _= 2*(1/(n+1)):= by
      rw[two_mul]

  have h': ((n:ℝ)+1) ≥ (2*k +2):= by
      norm_cast
      linarith
  have h'': 1/((n:ℝ)+1) ≤ 1/(2*k + 2):= by
      refine one_div_le_one_div_of_le ?ha h'
      linarith
  calc
    2*(1/((n:ℝ)+1)) ≤ 2*(1/(2*k + 2)):= by
        refine mul_le_mul ?h₁ h'' ?c0 ?b0
        rfl
        norm_num
        norm_cast
        norm_num
        norm_num
      _= 2*(1/(2*(k + 1))):= by
        rw [@mul_add_one]
      _= 1/(k + 1):= by
        simp
        norm_num
        rw [@mul_left_comm]
        simp
      _=(↑k + 1)⁻¹:= by
        norm_num

  simp at h
  suffices h': {x :ℍ | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1))\ ({0}:Set ℂ)}ᶜ ∪ {z:ℍ|↑z ∈ Metric.closedBall (0:ℂ) (1 / (k + 1))} = {z:ℍ|↑z ∈ Metric.closedBall (0:ℂ) (1 / (k + 1))} ∪ (⋃ i: (range (n)), {x:ℍ| ↑x ∈ complex_nth_hawaiian_circle i}) ∪ (⋃ (i: (range (2*k+1 - (n+1)))), {x:ℍ| ↑x ∈ complex_nth_hawaiian_circle (i + (n+1))})
  rw[h']
  repeat apply IsClosed.union
  simp
  apply isClosed_le
  apply Continuous.comp
  exact Complex.continuous_abs
  exact continuous_subtype_val
  exact continuous_const
  apply isClosed_iUnion_of_finite
  intro i
  unfold complex_nth_hawaiian_circle
  simp
  apply isClosed_eq
  apply Continuous.comp
  exact Complex.continuous_abs
  apply Continuous.sub
  exact continuous_subtype_val
  repeat exact continuous_const

  apply isClosed_iUnion_of_finite
  intro i
  unfold complex_nth_hawaiian_circle
  simp
  apply isClosed_eq
  apply Continuous.comp
  exact Complex.continuous_abs
  apply Continuous.sub
  exact continuous_subtype_val
  repeat exact continuous_const

  ext z
  constructor
  intro h'
  rcases h' with l|r

  have h₁: z∈ {x:ℍ| ↑x ∈ ℍ}:= by
    simp
  unfold hawaiian_earring_complex at h₁
  simp at h₁
  rcases h₁ with ⟨a,h₁⟩
  by_cases this: a = n
  simp at l
  simp
  repeat left
  suffices: ↑z = (0:ℂ)
  rw[this]
  norm_num
  norm_cast
  norm_num
  apply l
  unfold complex_nth_hawaiian_circle at h₁
  simp at h₁
  rw[this] at h₁
  exact h₁
  by_cases t₀: a < n
  simp
  left
  right
  use a

  by_cases t₁: a < 2*k + 1 -- ≥ than 2*k+1, then z is in the ball

  simp
  push_neg at this
  simp at t₀
  have h₂: a ≥ n + 1:= by
    exact Nat.lt_of_le_of_ne t₀ (id (Ne.symm this))
  right
  use a - (n+1)
  constructor
  rw [Nat.Simproc.sub_add_eq_comm]
  apply Nat.sub_lt_sub_right

  exact Nat.le_sub_one_of_lt h₂
  refine Nat.sub_lt_right_of_lt_add ?h.left.a.H t₁
  exact Nat.one_le_of_lt h₂
  rw [Nat.sub_add_cancel h₂]
  exact h₁

  repeat left -- want to show that the circle is inside the ball
  simp
  unfold complex_nth_hawaiian_circle at h₁
  simp at h₁
  calc
    Complex.abs (z) = Complex.abs (z - 1/(a+1) + 1/(a+1)):= by
      simp
    _≤ Complex.abs (z-1/(a+1)) + Complex.abs (1/(a+1)):=by
      exact AbsoluteValue.add_le Complex.abs (z - 1 / (a+1)) (1 / (a+1))
    _= (1/(a+1)) + (1/(a+1)):= by
        norm_num
        rw[h₁]
        norm_num
        norm_cast
        exact Complex.abs_natCast (a + 1)
    _= 2*(1/(a+1)):= by
        rw[two_mul]
  have h': ((a:ℝ)+1) ≥ (2*k +2):= by
      norm_cast
      linarith
  have h'': 1/((a:ℝ)+1) ≤ 1/(2*k + 2):= by
      refine one_div_le_one_div_of_le ?ha h'
  calc
    2*(1/((a:ℝ)+1)) ≤ 2*(1/(2*k + 2)):= by
        linarith
    _= 2*(1/(2*(k + 1))):= by
        rw [@mul_add_one]
    _= 1/(k + 1):= by
        simp
        norm_num
        rw [@mul_left_comm]
        simp
    _=(↑k + 1)⁻¹:= by
        norm_num

  repeat left
  exact r
   -- this was sorried to speed up the next bit of code

  -- reverse inclusion
  intro h'
  rcases h' with ((a|b)|c)
  right
  exact a
  unfold complex_nth_hawaiian_circle at b
  simp at b
  rcases b with ⟨a,bl,br⟩
  left
  simp
  intro h'
  apply circles_pairwise_intersection (1/(n+1)) (1/(a+1))
  simp
  linarith
  constructor
  simp
  exact h'
  simp
  exact br

  simp at c
  rcases c with ⟨a,cl,cr⟩
  simp
  left
  intro h'
  unfold complex_nth_hawaiian_circle at cr
  simp at cr
  apply circles_pairwise_intersection ((↑n + 1)⁻¹) ((↑a + (↑n + 1) + 1)⁻¹)
  simp
  norm_cast
  push_neg
  linarith
  constructor
  simp
  exact h'
  simp
  exact cr


lemma continuous_retract (n:ℕ): Continuous (my_function_res n):= by
  rw[my_function_res]
  apply Continuous.codRestrict -- may need to clean up function
  apply Continuous.piecewise
  intro z ⟨l,r⟩
  simp_all
  unfold complex_nth_hawaiian_circle at l r

  have h₀: ( fun x ↦ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1)) ↑x : Set ↑ℍ) = ({x | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1))} : Set ℍ):= by
    rfl
  rw[h₀] at r
  have h₁: @closure (↑ℍ) instTopologicalSpaceSubtype (fun x ↦ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1)) ↑x : Set ↑ℍ) = ({x | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1))} : Set ℍ):= by
    apply closure_eq_iff_isClosed.mpr
    rw[h₀]
    simp
    apply isClosed_eq
    apply Continuous.comp
    exact Complex.continuous_abs
    apply Continuous.sub
    exact continuous_subtype_val
    repeat exact continuous_const
  rw[h₁] at l
  suffices h₂: (z:ℂ) ∈ ({0}:Set ℂ)
  exact h₂

  suffices h₃: z ∉ ({x | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1)) \ ({0}:Set ℂ)})
  simp_all
  --suffices h₄: @interior (↑ℍ) instTopologicalSpaceSubtype ({x | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1))}) ⊇ ({x | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1)) \ ({0}:Set ℂ)})
  suffices h₄: ({x | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1)) \ ({0}:Set ℂ)}) ⊆ @interior (↑ℍ) instTopologicalSpaceSubtype ({x | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1))})
  contrapose h₄
  intro h
  push_neg at h₄
  have this: z ∈ @interior (↑ℍ) instTopologicalSpaceSubtype ({x | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1))}):= by
    exact h h₄
  contradiction

  suffices h₅: @IsOpen (↑ℍ) instTopologicalSpaceSubtype ({x | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1))\ ({0}:Set ℂ)})
  rw[interior]
  apply Set.subset_def.mpr
  intro a h
  apply Set.mem_sUnion.mpr
  use {x | ↑x ∈ Metric.sphere (1 / ((n:ℂ) + 1)) (1 / (n + 1))\ ({0}:Set ℂ)}
  simp only [Set.mem_diff, Complex.norm_eq_abs, Set.mem_singleton_iff,
    Set.mem_setOf_eq, Set.setOf_subset_setOf, and_imp, Subtype.forall]
  constructor
  constructor
  exact h₅
  intro x h' h'' h'''
  exact h''
  simp at h
  rcases h with ⟨l,r⟩
  constructor
  simp
  exact l
  exact r

  exact my_open_set_open n
  exact continuous_subtype_val
  exact continuous_const

-- Induced map between π₁(H) and π₁(Cₙ)
set_option maxHeartbeats 1000000000

def hawaiian_induced (n:ℕ):=
  (FundamentalGroupoid.fundamentalGroupoidFunctor.map (my_function_res n))

-- basic induced map

def my_induced_1:=
  (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Real.exp)).map

lemma exp_cts: Continuous (Real.exp):= by
  exact Real.continuous_exp

def exp_map_cts_class: C(ℝ,ℝ):= by
  use Real.exp
  exact Real.continuous_exp

-- product of induced maps (create a sequence of these maps)
--
def my_seq_map: ℝ → (ℕ → ℝ):= -- remember these sequences start from 0
  fun x ↦ (fun n ↦ Real.exp (n*x))

def my_seq_map1: ℝ → (ℕ → ℝ):= -- remember these sequences start from 0
  fun x ↦ (fun n ↦ Real.exp (n*x))

def my_map: ℝ → (Π (n:ℕ), ℝ):=
  fun x ↦ (fun y ↦ Real.exp (y*x))

def my_map1 (x): FundamentalGroup hawaiian_earring_complex (x) → Π (n:ℕ), FundamentalGroup (complex_nth_hawaiian_circle n (x)):=
  -- is this, by context, a direct product of groups?
  fun y ↦ (FundamentalGroupoid.fundamentalGroupoidFunctor.map ).map y
  sorry
def my_map2 (n:ℕ) (x) (y): FundamentalGroup hawaiian_earring_complex (x:ℍ) → FundamentalGroup (complex_nth_hawaiian_circle n) (y):=
  -- is this, by context, a direct product of groups?
  -- fun z ↦ (FundamentalGroupoid.fundamentalGroupoidFunctor.map (my_function_res n)).map z
  --fun z ↦ z.mapFn (my_function_res n)
  sorry

def my_map3 (x₀ x₁:ℝ) (P₀ : Path.Homotopic.Quotient x₀ x₁) (f : C(ℝ, ℝ)): Path.Homotopic.Quotient (f x₀) (f x₁):=
  --(FundamentalGroupoid.fundamentalGroupoidFunctor.map f)
  Path.Homotopic.Quotient.mapFn (P₀) f

def my_fun: unitInterval → ℝ:=
  fun x ↦ 0
lemma my_fun_cts: Continuous my_fun:= by
  exact continuous_of_const fun x ↦ congrFun rfl
def my_path:  Path (0:ℝ) (0:ℝ) where
  toFun:= my_fun
  continuous_toFun:= my_fun_cts
  source':= by
    simp
    rw[my_fun]
  target':= by
    simp
    rw[my_fun]

def my_exp: C(ℝ, ℝ) where -- need to use instances of structures to show objects are of a certain type
  toFun:= Real.exp

def real_space: TopologicalSpace ℝ where -- is this how you create topological space structure?
  sorry


def my_map4:=
   my_map3 (0) (0) (⟦my_path⟧) (my_exp)

-- let's try to apply this to ℍ

def retract_cts_class (n:ℕ): C(ℍ,complex_nth_hawaiian_circle n) where
  toFun:= my_function_res n
  continuous_toFun:= continuous_retract n

def Hawaiian_to_homotopy_class (x₀ :ℍ) (p : FundamentalGroup ℍ x₀):=
  @FundamentalGroup.toPath (TopCat.of ℍ) (x₀) (p)

def induced_retract (n:ℕ) (x₀:ℍ) (P₀ : Path.Homotopic.Quotient x₀ x₀):=
  Path.Homotopic.Quotient.mapFn (P₀) (retract_cts_class n)

def induced_image_to_nth_circle (n:ℕ) (x₀: complex_nth_hawaiian_circle n) (P₀ : Path.Homotopic.Quotient x₀ x₀):=
  @FundamentalGroup.fromPath (TopCat.of (complex_nth_hawaiian_circle n)) (x₀) (P₀)

def induced_retract_map_FG  (x₀:ℍ) (p : FundamentalGroup ℍ x₀) (n:ℕ):=
  @FundamentalGroup.fromPath (TopCat.of (complex_nth_hawaiian_circle n)) ((my_function_res n) x₀) (induced_retract (n) (x₀) (Hawaiian_to_homotopy_class (x₀) (p)))

-- Now, let's take the product of these maps to create a map to the fundamental group of the product space
def my_retract_product_map:= -- I think this map would be the same if I had put the x and n in the arguments, and then left them out
  fun x ↦ (fun n ↦ my_function_res n x)

def retract_product_cts_class: C(ℍ,Π (n:ℕ), complex_nth_hawaiian_circle n) where
  toFun:= my_retract_product_map
  continuous_toFun:= by
    unfold my_retract_product_map
    refine continuous_pi ?h
    intro n
    exact continuous_retract n

def induced_product_retract (x₀:ℍ) (P₀ : Path.Homotopic.Quotient x₀ x₀):=
  Path.Homotopic.Quotient.mapFn (P₀) (retract_product_cts_class)

-- This map is from π₁(ℍ) → π₁(∏ Cₙ)
def induced_product_map_FG (x₀:ℍ) (p:FundamentalGroup ℍ x₀):=
  @FundamentalGroup.fromPath (TopCat.of (Π (n:ℕ),complex_nth_hawaiian_circle n)) (my_retract_product_map x₀) (induced_product_retract (x₀) (Hawaiian_to_homotopy_class (x₀) (p)))

-- map from π₁(ℍ) → ∏ π₁(Cₙ)
def induced_product_map_FG1 (x₀:ℍ) (p:FundamentalGroup ℍ x₀): Π (n:ℕ), FundamentalGroup (↑(TopCat.of (↑(complex_nth_hawaiian_circle n)))) (my_function_res n x₀):=
  fun n ↦ @FundamentalGroup.fromPath (TopCat.of (complex_nth_hawaiian_circle n)) ((my_function_res n) x₀) (induced_retract n (x₀) (Hawaiian_to_homotopy_class (x₀) (p)))

-- This example shows the above def is obselete
example(x₀:ℍ) (p:FundamentalGroup ℍ x₀): induced_product_map_FG1 (x₀) (p) = induced_retract_map_FG (x₀:ℍ) (p:FundamentalGroup ℍ x₀):= by
  rfl
-- May not neeed this
example (x₀: ℍ): FundamentalGroup (↑(TopCat.of ((n : ℕ) → ↑(complex_nth_hawaiian_circle n)))) (my_retract_product_map x₀) ≅ Π (n:ℕ), FundamentalGroup (↑(TopCat.of (↑(complex_nth_hawaiian_circle n)))) (my_function_res n x₀):= by
  simp
  sorry

-- Induced maps using TopCatOf: may be more straightforward

def map_1 (n:ℕ):=
  FundamentalGroupoid.fundamentalGroupoidFunctor.map (retract_cts_class n)
  sorry


-- Showing that the induced product map from π₁(ℍ) to Π ℤ is surjective

open Complex

def nth_hawaiian_sequence_loop (n:ℕ) (aₙ:ℤ): ℝ → ℂ :=
  fun t ↦ 1/(n+1) - 1/(n+1)*exp ((2*Real.pi*aₙ*(n+1)*(n+2)*((t-(1-((1/((n)+1)):ℝ)))))*I)

-- this definition does not add 1 to everything, this was changed to make the sequence map to all circles, not just the second one onwards
def nth_hawaiian_sequence_loop1 (n:ℕ) (aₙ:ℤ): ℝ → ℂ :=
  fun t ↦ 1/(n) - 1/(n)*exp ((2*Real.pi*aₙ*(n)*(n+1)*((t-(1-((1/((n))):ℝ)))))*I)


lemma nth_hawaiian_sequence_loops_maps_to_hawaiian_earring (n:ℕ) (aₙ:ℤ):  Set.MapsTo (nth_hawaiian_sequence_loop n aₙ) (Set.Icc (1-1/((n:ℝ)+1)) (1-1/((n:ℝ)+2))) (ℍ):= by
  rw[Set.MapsTo]
  intro t
  intro h
  rw[nth_hawaiian_sequence_loop]
  rw[hawaiian_earring_complex]
  apply Set.mem_iUnion.mpr
  use n
  rw[complex_nth_hawaiian_circle]
  simp
  norm_cast
  calc
    _= (Complex.abs ↑(n + 1))⁻¹ * Complex.abs (cexp (↑(2 * Real.pi * ↑aₙ * ↑(n + 1) * ↑(n + 2) * (t - (↑(n + 1))⁻¹))*I) ):= by
      simp
    _= (Complex.abs ↑(n + 1))⁻¹ * 1:= by
      rw[abs_exp_ofReal_mul_I]
  simp
  norm_cast
  exact abs_natCast (n + 1)

def nth_hawaiian_sequence_loops_restricted (n:ℕ) (aₙ:ℤ):=
  Set.MapsTo.restrict (nth_hawaiian_sequence_loop (n) (aₙ)) (Set.Icc (1-1/((n:ℝ)+1)) (1-1/((n:ℝ)+2))) (ℍ) (nth_hawaiian_sequence_loops_maps_to_hawaiian_earring n aₙ)

-- This is not well defined for t = 1 in [0,1], define piecwise instead?
def hawaiian_sequence_loops (a : Π (n:ℕ), ℤ): ℝ → ℂ:=
  fun t ↦ nth_hawaiian_sequence_loop1 (Nat.floor (1/(1-t))) (a (Nat.floor (1/(1-t)))) (t)

def hawaiian_sequence_loops_piecewise (a : Π (n:ℕ), ℤ): ℝ → ℂ:=
  Set.piecewise (Set.Ico 0 1) (fun t ↦ nth_hawaiian_sequence_loop1 (Nat.floor (1/(1-t))) (a (Nat.floor (1/(1-t)))) (t)) (fun t ↦ 0)
-- How do you make this local in the proof below?
def special_floor:=
  fun t ↦ Nat.floor (1/(1-t))

lemma hawaiian_sequence_loops_maps_to_hawaiian_earring (a : Π (n:ℕ), ℤ): Set.MapsTo (hawaiian_sequence_loops a) (unitInterval) (ℍ):= by
  rw[Set.MapsTo]
  intro t
  intro h
  rw[hawaiian_sequence_loops]
  rw[nth_hawaiian_sequence_loop]
  rw[hawaiian_earring_complex]
  simp
  use Nat.floor (1/(1-t))
  rw[complex_nth_hawaiian_circle]
  simp
  norm_cast
  calc
    _=(Complex.abs ↑(⌊(1 - t)⁻¹⌋₊ + 1))⁻¹ * Complex.abs (cexp (↑((2 * Real.pi * ↑(a ⌊(1 - t)⁻¹⌋₊) * ↑(⌊(1 - t)⁻¹⌋₊ + 1) * ↑(⌊(1 - t)⁻¹⌋₊ + 2)) *(t - (↑(⌊(1 - t)⁻¹⌋₊ + 1))⁻¹)) *
          I)):= by
          simp
    _= (Complex.abs ↑(⌊(1 - t)⁻¹⌋₊ + 1))⁻¹ * 1:= by
      rw[abs_exp_ofReal_mul_I]
  simp
  norm_cast
  apply abs_natCast
  sorry



lemma hawaiian_sequence_loops_piecewise_maps_to_hawaiian_earring (a : Π (n:ℕ), ℤ): Set.MapsTo (hawaiian_sequence_loops_piecewise a) (unitInterval) (ℍ):= by
  rw[Set.MapsTo]
  intro t
  intro h
  rw[hawaiian_sequence_loops_piecewise]
  simp
  by_cases h': t ∈ Set.Ico 0 1
  rw[Set.piecewise_eq_of_mem]
  rw[nth_hawaiian_sequence_loop1]
  rw[hawaiian_earring_complex]
  simp
  use Nat.floor (1/(1-t)) - 1
  rw[complex_nth_hawaiian_circle]
  simp
  norm_cast
  have h'': max (Nat.floor ((1-t)⁻¹)) (1) = Nat.floor ((1-t)⁻¹):= by
    simp
    rw[Set.Ico] at h'
    simp at h'
    rcases h' with ⟨l,r⟩
    refine one_le_inv ?h₁ ?h₂
    simp
    exact r
    simp
    exact l

  calc
    _=  Complex.abs ((↑⌊(1 - t)⁻¹⌋₊)⁻¹ - (↑(⌊(1 - t)⁻¹⌋₊ - 1 + 1))⁻¹ - (↑⌊(1 - t)⁻¹⌋₊)⁻¹ * cexp
            (↑(2 * Real.pi * ↑(a ⌊(1 - t)⁻¹⌋₊) * ↑⌊(1 - t)⁻¹⌋₊ * ↑(⌊(1 - t)⁻¹⌋₊ + 1)) * (↑t - (1 - (↑⌊(1 - t)⁻¹⌋₊)⁻¹) )*I)):= by
              repeat rw[Nat.sub_add_eq_max]
              simp
              rw [@sub_right_comm]


    _=  Complex.abs (-(↑⌊(1 - t)⁻¹⌋₊)⁻¹ * cexp
            (↑(2 * Real.pi * ↑(a ⌊(1 - t)⁻¹⌋₊) * ↑⌊(1 - t)⁻¹⌋₊ * ↑(⌊(1 - t)⁻¹⌋₊ + 1)) * (↑t - (1 - (↑⌊(1 - t)⁻¹⌋₊)⁻¹)) * I)):= by
              rw[Nat.sub_add_eq_max]
              rw[h'']
              simp
  simp
  calc
    _= (↑⌊(1 - t)⁻¹⌋₊)⁻¹ *
    Complex.abs
      (cexp (↑(2 * Real.pi * ↑(a ⌊(1 - t)⁻¹⌋₊) * ↑⌊(1 - t)⁻¹⌋₊ * (↑⌊(1 - t)⁻¹⌋₊ + 1) * (t - (1- (↑⌊(1 - t)⁻¹⌋₊)⁻¹)) )*I)):= by
        simp
    _= (↑⌊(1 - t)⁻¹⌋₊)⁻¹ * 1:= by
      rw[abs_exp_ofReal_mul_I]
  simp
  rw[←h'']
  simp
  exact h'


  rw[Set.piecewise_eq_of_not_mem]
  rw[hawaiian_earring_complex]
  simp
  use 1
  rw[complex_nth_hawaiian_circle]
  simp
  norm_cast
  norm_num
  exact h'

def hawaiian_sequence_loops_restricted (a : Π (n:ℕ), ℤ): unitInterval → ℍ:=
  Set.MapsTo.restrict (hawaiian_sequence_loops (a)) (unitInterval) (ℍ) (hawaiian_sequence_loops_maps_to_hawaiian_earring a)

def hawaiian_sequence_loops_piecewise_restricted (a : Π (n:ℕ), ℤ): unitInterval → ℍ:=
  Set.MapsTo.restrict (hawaiian_sequence_loops_piecewise (a)) (unitInterval) (ℍ) (hawaiian_sequence_loops_piecewise_maps_to_hawaiian_earring a)

lemma floor_max_helper (t:ℝ) (h: t ∈ Set.Ico 0 1): max (Nat.floor ((1-t)⁻¹)) (1) = Nat.floor ((1-t)⁻¹):= by
  simp
  rw[Set.Ico] at h
  simp at h
  rcases h with ⟨l,r⟩
  refine one_le_inv ?h₁ ?h₂
  simp
  exact r
  simp
  exact l

lemma hawaiian_sequence_loops_piecewise_continuous (a: Π (n:ℕ), ℤ): Continuous (hawaiian_sequence_loops_piecewise_restricted a):= by
  /-rw[hawaiian_sequence_loops_piecewise_restricted]
  apply Continuous.restrict
  apply Continuous.piecewise
  intro x h
  rw[nth_hawaiian_sequence_loop1]
  simp
  have h₀: frontier (Set.Ico 0 1) = {(0:ℝ),(1:ℝ)}:= by
    apply frontier_Ico
    norm_num
  rw[h₀] at h
  simp at h
  rcases h with (x0|x1)
  rw[x0]
  simp
  rw[x1]
  simp-/

  rw[hawaiian_sequence_loops_piecewise_restricted]
  apply Continuous.restrict
  apply continuous_piecewise
  intro x h
  rw[nth_hawaiian_sequence_loop1]
  simp
  have h₀: frontier (Set.Ico 0 1) = {(0:ℝ),(1:ℝ)}:= by
    apply frontier_Ico
    norm_num
  rw[h₀] at h
  simp at h
  rcases h with (x0|x1)
  rw[x0]
  simp
  rw[x1] -- this worked, even though t=1 is not well defined?
  simp

  simp

  -- ExtraTODO (XTODO) (list 1): this argument should be generalised in a lemma for constant functions
  have h₀ (n:ℕ): ContinuousOn (hawaiian_sequence_loops a) (Set.Icc (1-1/(n+1:ℝ)) (1-1/((n+2)))):= by
    unfold hawaiian_sequence_loops
    unfold nth_hawaiian_sequence_loop1


    intro x h'

    apply ContinuousOn.sub
    apply ContinuousOn.div₀
    exact continuousOn_const

    apply continuousOn_iff_continuous_restrict.mpr
    suffices: (Set.Icc (1 - 1 / (↑(n:ℝ) + 1)) (1 - 1 / (↑(n:ℝ) + 2))).restrict (fun (x:ℝ) ↦ (↑⌊1 / (1 - x)⌋₊:ℂ)) = fun x ↦ (n:ℂ) + 1
    rw[this]
    exact continuous_const
    ext t
    simp
    have h: (t:ℝ) ∈ Set.Icc (1 - 1/(↑(n:ℝ) + 1)) (1 - 1/(↑(n:ℝ) + 2)):= by
      exact Subtype.coe_prop t-- ExtraTODO: easy way to do this?
    rcases h with ⟨l,r⟩
    simp at l
    norm_cast
    refine (Nat.floor_eq_iff' ?this.h.intro.ha).mpr ?this.h.intro.a
    norm_num
    constructor
    simp
    suffices: 1/(n+1) ≥1/( (1 - (t:ℝ))⁻¹)
    apply le_of_one_div_le_one_div
    norm_num
    calc
      _≤1 - 1 / (↑n + 2):= r
      _<1:= by
        simp
        norm_cast
        norm_num
    exact this
    simp
    linarith
    simp
    apply lt_of_one_div_lt_one_div
    norm_cast
    simp
    simp




    -- show between n+1 and n+2



  have h₁: Set.Ico (0:ℝ) (1:ℝ) = ⋃ (n:ℕ), Set.Icc ((1-1/((n+1):ℝ))) ((1-1/(n+2))):= by
    ext x
    constructor
    rintro ⟨l,r⟩
    simp
    use Nat.floor (1/(1-x)) - 1-- change?
    simp
    constructor
    norm_cast
    rw[Nat.sub_add_eq_max]
    rw[floor_max_helper]
    suffices: 1 - x ≤ (↑⌊(1 - x)⁻¹⌋₊)⁻¹
    linarith
    suffices: 1/(1-x) ≥ 1/((↑⌊(1 - x)⁻¹⌋₊)⁻¹)
    have h: 1/(1/(1-x)) ≤ 1/(1/(↑⌊(1 - x)⁻¹⌋₊)⁻¹):= by --XTODO: clean this up with simple theorems
      refine one_div_le_one_div_of_le ?ha this
      simp
      rw [@Nat.floor_pos]
      rw[←one_div]
      refine one_le_one_div ?ha.h1 ?ha.h2
      simp
      exact r
      simp
      exact l
    linarith
    simp
    refine Nat.floor_le ?this.ha
    simp
    linarith
    simp
    exact ⟨l,r⟩

    norm_cast
    have h: 2 = 1 + 1:= by
      exact rfl
    rw[h]
    norm_cast
    rw[←add_assoc]
    rw[Nat.sub_add_eq_max]
    rw[floor_max_helper]
    suffices: 1-x ≥ (↑(⌊(1 - x)⁻¹⌋₊+1))⁻¹
    linarith
    suffices: 1/(1-x) ≤ 1/((↑(⌊(1 - x)⁻¹⌋₊ + 1))⁻¹)
    have h: 1/(1/(1-x)) ≥ 1/(1/(↑(⌊(1 - x)⁻¹⌋₊+1))⁻¹):= by
      apply one_div_le_one_div_of_le
      simp
      exact r
      exact this
    linarith
    simp


    apply le_trans
    apply Nat.le_ceil
    norm_cast
    apply Nat.ceil_le_floor_add_one
    exact ⟨l,r⟩

    intro h
    simp at h
    simp
    rcases h with ⟨n,l,r⟩
    constructor
    suffices: x+1 ≥ 1
    linarith
    apply ge_trans
    suffices: x+1 ≥ x + 1/(n+1)
    apply this
    simp
    norm_cast
    exact Nat.cast_inv_le_one (n + 1)
    simp
    exact l

    calc
      x ≤ 1 - ((↑n+2))⁻¹:= by
        exact r
      _<1:= by
        simp
        norm_cast
        norm_num


  have h₂: Set.Icc (0:ℝ) (1:ℝ) = Set.Ico (0:ℝ) (1:ℝ) ∪ {1}:= by
    refine Eq.symm (Set.Ico_union_right ?hab)
    norm_num
  --rw[h₂]

 /-suffices: ContinuousOn (hawaiian_sequence_loops a) (Set.Ico 0 1) ∧  ContinuousOn (hawaiian_sequence_loops a) ({1})
  rcases this with ⟨l,r⟩
  unfold hawaiian_sequence_loops at l r-/


  --case where t<1
  --rw[h₁]
  intro x h
  by_cases h': x ∈ Set.Ico 0 1
  rw[h₁] at h'
  simp at h'
  rcases h' with ⟨n,l,r⟩
  by_cases h'': 1 < x + ((n:ℝ)+1)⁻¹
  unfold nth_hawaiian_sequence_loop1



  --apply LocallyFinite.continuousOn_iUnion

  sorry

  --intro n
  --exact isClosed_Icc

  -- want ctsOn the piecewise subset.



-- This is how you define 0 and other numbers as a subtype.
def zero_hawaiian: ℍ:= by
  use 0
  rw[hawaiian_earring_complex]
  simp
  use 1
  rw[complex_nth_hawaiian_circle]
  simp
  norm_cast
  norm_num

def hawaiian_sequence_loops_as_path (a: Π (n:ℕ), ℤ): Path (zero_hawaiian) (zero_hawaiian) where
  toFun := hawaiian_sequence_loops_piecewise_restricted a
  continuous_toFun:= hawaiian_sequence_loops_piecewise_continuous a
  source' := by
    simp
    rw[hawaiian_sequence_loops_piecewise_restricted ]
    refine SetCoe.ext ?_
    simp
    rw[hawaiian_sequence_loops_piecewise]
    simp
    rw[nth_hawaiian_sequence_loop1]
    simp
    rw[zero_hawaiian]
  target' := by
    simp
    rw[hawaiian_sequence_loops_piecewise_restricted ]
    refine SetCoe.ext ?_
    simp
    rw[hawaiian_sequence_loops_piecewise]
    simp
    rw[zero_hawaiian]


-- Gives an element in ∏ π₁(Cₙ)
def hawaiian_path_as_FG (a: ℕ → ℤ):=
  @FundamentalGroup.fromPath (TopCat.of ℍ) zero_hawaiian ⟦hawaiian_sequence_loops_as_path a⟧

def induced_path_circle_FG (a: ℕ → ℤ):=
  induced_retract_map_FG (zero_hawaiian) (hawaiian_path_as_FG a)


-- Showing that Π π₁(Cₙ) ≅ Π ℤ

-- TODO: Help finish/implement proof of π₁(S¹) ≅ ℤ.

-- this works in the first steps file but not here! Put these in external files, this should solve the issue
-- use definitions instead, that's what mathlib does. This is the isomorphism structure, given to the map.
def fundamental_group_hawaiian_circle (n : ℕ) (x₀) : FundamentalGroup (complex_nth_hawaiian_circle n) (x₀) ≃* ℤ where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

-- This map was not needed as pi types can reduce to the above fact^
-- As this is a product isomorphism, may be able to use the fact Aₙ ≅ Bₙ ∀n ∈ ℕ, then Π (n:ℕ), Aₙ ≅ Π (n:ℕ), Bₙ (or more generally for an indexed set I (I think))
def product_isomorphism (x₀:ℍ): (Π (n:ℕ), FundamentalGroup (complex_nth_hawaiian_circle n) (my_function_res n x₀)) ≃* Π (n:ℕ), ℤ where
  toFun := fun a ↦ (fun n ↦ (fundamental_group_hawaiian_circle n (my_function_res n x₀)).toFun (a n))
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry



-- fractional expansion method

noncomputable section -- why do I have to put this here?

@[simp]
def my_frac_expansion_function:=
  (fun (x : ℝ) ↦ (SimpContFract.of x))

@[simp]
def my_frac_expansion_function':=
  (fun (x : ℝ) ↦ (GenContFract.of x))

@[simp]
def my_stream_function:=
  (fun (x : ℝ) ↦ (GenContFract.of x).convs)

example: ℝ ↪ (SimpContFract ℝ):= by
  refine { toFun := ?toFun, inj' := ?inj' }
  use my_frac_expansion_function
  intro a b h
  simp_all
  apply?

-- XTODO: Convert this into filters language to make it more Mathlib friendly
lemma helper1 [TopologicalSpace ℝ] [T2Space ℝ] (u : ℕ → ℝ) {a b : ℝ} (ha : Filter.Tendsto u Filter.atTop (nhds a))
    (hb : Filter.Tendsto u Filter.atTop (nhds b)) : a = b :=
  tendsto_nhds_unique ha hb

-- from mathematics in lean
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a- s n| < ε
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
    sorry

example: ℝ ↪ (GenContFract ℝ):= by
  refine { toFun := ?toFun, inj' := ?inj' }
  use my_frac_expansion_function'
  intro a b h
  simp_all
  have h' (n:ℕ): (GenContFract.of a).convs n = (GenContFract.of b).convs n:= by
    rw[h]
  have h'': ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, |a - (GenContFract.of a).convs n| < ε:= by
    exact fun ε a_1 ↦ GenContFract.of_convergence_epsilon a ε a_1
  have h'''': ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, |b - (GenContFract.of a).convs n| < ε:= by
    rw[h]
    exact fun ε a ↦ GenContFract.of_convergence_epsilon b ε a
  apply convergesTo_unique h'' h''''

@[simp]
def helper2: (SimpContFract ℝ) → (ℕ → Option ℝ):= by
  exact fun a ↦ fun n ↦ (a:GenContFract ℝ).partDens.get? n



example: (SimpContFract ℝ) ↪ (ℕ → Option ℝ):= by
  refine { toFun := ?toFun, inj' := ?inj' }
  use helper2
  intro a b h
  sorry

example: (SimpContFract ℝ) → (ℕ → Option ℤ):= by
  exact fun a ↦ (fun n ↦ (a:GenContFract ℝ).partDens.get? n)


example: ℝ ↪ (Stream' ℝ):= by
  refine { toFun := ?toFun, inj' := ?inj' }
  use my_stream_function
  intro a b h
  simp_all


-- binary sequence approach



-- Statement of the theorem --
-- we do not need inequality here, we only need ≤
lemma cardinality_reals_eq_prod_integers: Cardinal.mk (ℝ) = Cardinal.mk (Π (n:ℕ), ℤ):= by
  simp
  exact Cardinal.mk_real

-- TODO: This argument should be generalised to show that an isomorphism between two things implies a bijection (probably already in library)
/-lemma cardinality_eq (x₀:ℍ) (n:ℕ):  Cardinal.mk (ℤ) = Cardinal.mk ( FundamentalGroup (complex_nth_hawaiian_circle n) (my_function_res n x₀)):= by
  refine Cardinal.mk_congr ?e
  refine (Equiv.ofBijective ?e.f ?e.hf).symm
  use (fundamental_group_hawaiian_circle n (my_function_res n x₀)).toFun
  constructor
  apply Function.HasLeftInverse.injective
  rw[Function.HasLeftInverse]
  use (fundamental_group_hawaiian_circle n (my_function_res n x₀)).invFun
  use (fundamental_group_hawaiian_circle n (my_function_res n x₀)).left_inv

  apply Function.HasRightInverse.surjective
  rw[Function.HasRightInverse]
  use (fundamental_group_hawaiian_circle n (my_function_res n x₀)).invFun
  use (fundamental_group_hawaiian_circle n (my_function_res n x₀)).right_inv-/

-- Uses the proof of the above, had an annoying issue where unknown variable could not be defined before it was used
lemma cardinality_pi_int_eq_pi_circle (x₀:ℍ): Cardinal.mk (Π (n:ℕ), ℤ) = Cardinal.mk (Π (n:ℕ), FundamentalGroup (complex_nth_hawaiian_circle n) (my_function_res n x₀)):= by
  apply Cardinal.mk_congr
  refine Equiv.piCongrRight ?e.F
  intro n
  apply Equiv.ofBijective ?e.F.f ?e.F.hf
  use (fundamental_group_hawaiian_circle n (my_function_res n x₀)).invFun
  constructor
  apply Function.HasLeftInverse.injective
  rw[Function.HasLeftInverse]
  use (fundamental_group_hawaiian_circle n (my_function_res n x₀)).toFun
  use (fundamental_group_hawaiian_circle n (my_function_res n x₀)).right_inv

  apply Function.HasRightInverse.surjective
  rw[Function.HasRightInverse]
  use (fundamental_group_hawaiian_circle n (my_function_res n x₀)).toFun
  use (fundamental_group_hawaiian_circle n (my_function_res n x₀)).left_inv

-- instance needed
instance hawaiian_earring_as_path_connected_space: PathConnectedSpace ↑ℍ:= by
  refine isPathConnected_iff_pathConnectedSpace.mp ?_
  exact isPathConnected_hawaiian_earring

def FG_isomorphism (x:hawaiian_earring_complex): FundamentalGroup (hawaiian_earring_complex:Set ℂ) (x) ≃* FundamentalGroup (hawaiian_earring_complex: Set ℂ) (zero_hawaiian):= by
  apply FundamentalGroup.fundamentalGroupMulEquivOfPathConnected

lemma cardinality_fundamental_group_hawaiian_earring_independent_of_basepoint (x): Cardinal.mk (FundamentalGroup hawaiian_earring_complex x) = Cardinal.mk (FundamentalGroup hawaiian_earring_complex (zero_hawaiian)):= by
  refine Cardinal.mk_congr ?e
  refine (Equiv.ofBijective ?e.f ?e.hf)
  use (FG_isomorphism x).toFun
  constructor
  refine Function.HasLeftInverse.injective ?e.hf.left.a
  rw[Function.HasLeftInverse]
  use (FG_isomorphism x).invFun
  use (FG_isomorphism x).left_inv
  refine Function.HasRightInverse.surjective ?e.hf.right.a
  rw[Function.HasRightInverse]
  use (FG_isomorphism x).invFun
  use (FG_isomorphism x).right_inv


theorem fundamental_group_hawaiian_earring_uncountable (x): Cardinal.mk (FundamentalGroup hawaiian_earring_complex x) ≥ Cardinal.continuum:= by
  rw[←Cardinal.mk_real]
  rw[cardinality_reals_eq_prod_integers]
  rw[cardinality_pi_int_eq_pi_circle x]
  rw[cardinality_fundamental_group_hawaiian_earring_independent_of_basepoint x]

  apply Cardinal.mk_le_of_injective
  sorry
  sorry

-- binary sequence approach
-- XTODO: more general version of this lemma (consequence of cantor_surjective)
lemma nat_cardinality_lt_set_of_nat: Cardinal.mk (ℕ) < Cardinal.mk (Set ℕ):= by
  simp
  exact Cardinal.aleph0_lt_continuum

lemma set_of_binary_sequences_cardinality_eq_set_of_nat:  Cardinal.mk (Set ℕ) = Cardinal.mk (ℕ → ({0,1} :Set ℕ)):= by
  simp

theorem fundamental_group_hawaiian_earring_uncountable1 (x): Uncountable (FundamentalGroup ℍ x):= by
  suffices: Cardinal.mk (FundamentalGroup hawaiian_earring_complex x) > Cardinal.mk (ℕ)
  refine uncountable_iff_isEmpty_embedding.mpr ?_
  apply Cardinal.mk_eq_zero_iff.mp
  apply Cardinal.mk_embedding_eq_zero_iff_lt.mpr
  exact this
  rw [cardinality_fundamental_group_hawaiian_earring_independent_of_basepoint]
  apply lt_of_lt_of_le
  apply nat_cardinality_lt_set_of_nat
  rw[set_of_binary_sequences_cardinality_eq_set_of_nat]
  apply Cardinal.mk_le_of_injective
  sorry
  sorry



-- practice examples to help me understand things

-- lesson learned: needed instance, not def or lemma below for def mine to work
instance blah: PathConnectedSpace (@Set.Elem ℝ Set.univ):= by
  refine isPathConnected_iff_pathConnectedSpace.mp ?_
  exact isPathConnected_univ

def mine (x)(y): FundamentalGroup (@Set.univ ℝ) (x) ≃* FundamentalGroup (@Set.univ ℝ) (y):= by
  apply FundamentalGroup.fundamentalGroupMulEquivOfPathConnected




  --refine PathConnectedSpace.somePath x y

def my_inclusion (X: Set ℂ): ↥X → ℂ:=
  fun z ↦ z
set_option maxHeartbeats 0

example: @IsClosed (↥(Metric.closedBall (0:ℂ) 2)) instTopologicalSpaceSubtype ({z| ↑z ∈ Metric.closedBall (0:ℂ) (1)}):= by
  simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_eq_abs]
  apply isClosed_le
  apply Continuous.comp
  exact Complex.continuous_abs
  exact continuous_subtype_val
  exact continuous_const


example: @closure (↑ℍ) instTopologicalSpaceSubtype ({x | ↑x ∈ Metric.sphere (0:ℂ) 1}: Set ↑ℍ) = ({x | ↑x ∈ Metric.sphere (0:ℂ) 1} : Set ℍ):= by
  apply closure_eq_iff_isClosed.mpr
  simp
  apply isClosed_eq
  apply Continuous.comp
  exact Complex.continuous_abs
  exact continuous_subtype_val
  exact continuous_const

/-def C_top: TopologicalSpace ℂ:=
  StandardTop

def my_induced:=
  TopologicalSpace.induced (my_inclusion ℍ) ()-/




-- A subset of a closed subspace is closed in the whole space and vice verse
example (X: Set ℂ) (C: Set ℂ) (h₀: C ⊆ X) (h₁: IsClosed C): ∀(S : Set ℂ), S ⊆ C ∧ @IsClosed (↥C) instTopologicalSpaceSubtype ({x| ↑x ∈ S}) ↔ IsClosed S:= by
  intro S
  constructor
  rintro ⟨l,r⟩
  apply isOpen_compl_iff.mp
  sorry

  intro h
  constructor
  sorry
  sorry

-- Subspace topology def
example (X : Set ℂ) (U: Set ℂ): @IsOpen (↥X) instTopologicalSpaceSubtype ({x| ↑x ∈ U}) ↔ ∃ (V : Set ℂ), IsOpen V ∧ ↑U = V ∩ X:= by
  constructor
  intro h

def ex_function: ℝ → ℝ:=
  Set.piecewise (Set.Icc (0:ℝ) 1) (fun x ↦ 0) (fun x ↦ 1)

def ex_function0: ℝ → ℝ:=
  (fun x ↦ 0)

example: ex_function '' (Set.Icc (0:ℝ) (1)) = {0}:= by
  ext x
  constructor
  intro h
  rcases h with  ⟨y,l,r⟩
  rw[ex_function] at r
  have h': (Set.Icc 0 1).piecewise (fun x ↦ 0) (fun x ↦ 1) y = 0:= by
    exact Set.piecewise_eq_of_mem (Set.Icc 0 1) (fun x ↦ 0) (fun x ↦ 1) l
  rw[h'] at r


def ex_function1: {x:ℝ // x≤0} → ℝ:=
  fun x ↦ 0

def ex_function2: {x:ℝ // x≤0} → ℝ:=
  Set.piecewise ({x|x≤(0:ℝ)}) (fun x ↦ 0) (fun x ↦ 1)

def ex_function3: ℝ → Set.Icc (0:ℝ) 1:=
  Set.piecewise (Set.Icc (0) (1)) (fun x ↦ 0) (fun x ↦ 1)

def ex_function4: Set.Icc (1:ℝ) 2 → ℝ:=
  Set.piecewise ({(x: ℝ)| x∈ Set.Icc (0) (1)}) (fun x ↦ 0) (fun x ↦ 1)

def ex_function5: Set.Icc (1:ℝ) 2 → Set.Icc (0:ℝ) 1:=
  ex_function3 ∘ ex_function4

lemma is_cts: Continuous ex_function1:= by
  exact continuous_of_const fun x ↦ congrFun rfl

example: Continuous ex_function2:= by
  apply Continuous.piecewise
  intro a h
  sorry

-- this example shows this works on Subspace topology

--π₁(S¹) ≅ ℤ
--ℍ
--π₁(ℍ,0)
/-
nformally, given any sequence of integers (aₖ), we can “encode” this sequence on H.
How? Well we can take the homotopy class of a loop in a similar fashion to right hand side figure. Explicitly, we can take the functions-/
-- pₐₖ
-- ∀k
-- Cₙ
