module

public import Theory.Character.CyclicThirteenNormalizer
public import Theory.Character.InductionSpecialSupportExtraction

/-!
# Ambient exceptional characters for an order-thirteen subgroup

The punctured subgroup of order thirteen is a special support in its
normalizer: a transporter of generators normalizes the subgroup. Differences
of the four local cubic characters are supported there, since they have equal
degrees and vanish off the subgroup. Induction is therefore an integral
isometry on their difference lattice. Peterfalvi (1.4) extracts four distinct
ambient irreducibles with equal positive degrees and a common sign.

The final API records all pairwise induced differences, their restrictions,
and an embedding into any complete ambient character family. It makes no
block-membership assertion; identifying the block is a subsequent step.

Source: the exceptional-character construction underlying
Alperin--Brauer--Gorenstein, III.8, printed pp.116--117; Peterfalvi (1.4).
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace CyclicThirteenNormalizer
variable {G : Type*} [Group G] [Finite G] {P : Subgroup G}

/-- A nonidentity element generates a prime-order subgroup, so a transporter
between its nonidentity elements normalizes the subgroup. -/
theorem transporter_mem_normalizer (hP : Nat.card P = 13) (a b : P) (ha : a ≠ 1)
    (g : G) (hg : g⁻¹ * (a : G) * g = (b : G)) : g ∈ Normalizer P := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  apply (Normalizer P).inv_mem_iff.mp
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  obtain ⟨n, hn⟩ := mem_powers_of_prime_card hP (g' := (⟨x,hx⟩ : P)) ha
  have hn' : (a : G) ^ n = x := congrArg Subtype.val hn
  rw [← hn']
  have hh : g⁻¹ * (a : G) ^ n * g = (g⁻¹ * (a : G) * g) ^ n := by
    simpa using map_pow (MulAut.conj g⁻¹) (a : G) n
  simp only [inv_inv, hh, hg]
  exact P.pow_mem b.property n

@[expose] def specialSupport (P : Subgroup G) : Set (Normalizer P) :=
  {a | a ∈ core P ∧ a ≠ 1}

theorem specialSupport_transporters (hP : Nat.card P = 13) :
    ∀ a b : Normalizer P, a ∈ specialSupport P → b ∈ specialSupport P →
      ∀ g : G, g⁻¹ * (a : G) * g = (b : G) → g ∈ Normalizer P := by
  intro a b ha hb g hg
  apply transporter_mem_normalizer hP (⟨a,ha.1⟩ : P) (⟨b,hb.1⟩ : P) _ g hg
  intro he
  exact ha.2 (Subtype.ext (congrArg (fun x : P => (x : G)) he))

@[expose] def Rows.localClass (s : Rows P) (i : Fin 4) : ClassFunction (Normalizer P) :=
  ofConjClassFunction (s.chi i)

theorem Rows.localClass_basis (s : Rows P) :
    Section1.IsIrreducibleCharacterBasis s.localClass := by
  refine ⟨fun i => Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup
    (s.irreducible i), ?_⟩
  intro i j hij he
  apply hij
  apply s.distinct
  ext c
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
  exact congrFun he g

theorem Rows.difference_supported (s : Rows P) (i j : Fin 4) :
    supportedOn (s.localClass i - s.localClass j) (specialSupport P) := by
  intro a ha
  change s.chi i (ConjClasses.mk a) - s.chi j (ConjClasses.mk a) = 0
  by_cases h1 : a = 1
  · rw [h1, s.degree, s.degree, sub_self]
  · have hc : a ∉ core P := fun hc => ha ⟨hc,h1⟩
    rw [s.vanish i a hc, s.vanish j a hc, sub_self]

theorem Rows.induction_isometry (s : Rows P) (hP : Nat.card P = 13) (i j k l : Fin 4) :
    scalarProduct G
      (inducedClassFunction (Normalizer P) (s.localClass i - s.localClass j))
      (inducedClassFunction (Normalizer P) (s.localClass k - s.localClass l)) =
    scalarProduct (Normalizer P) (s.localClass i - s.localClass j)
      (s.localClass k - s.localClass l) := by
  apply scalarProduct_inducedClassFunction_of_specialSupport (Normalizer P)
    (specialSupport P) (specialSupport_transporters hP)
  · intro x g
    change ofConjClassFunction (s.chi k) (g*x*g⁻¹) -
      ofConjClassFunction (s.chi l) (g*x*g⁻¹) = _
    rw [ofConjClassFunction_isClassFunction, ofConjClassFunction_isClassFunction]
    rfl
  · exact s.difference_supported i j
  · exact s.difference_supported k l

/-- Induction supplies the integer lattice isometry in Peterfalvi (1.4),
with respect to any complete ambient irreducible family and its degrees. -/
theorem Rows.integral_isometry (s : Rows P) (hP : Nat.card P = 13)
    {J : Type*} [Fintype J] [DecidableEq J]
    (μ : J → ConjClassFunction G) (hμ : IsCompleteIrreducibleCharacterFamily μ)
    (d : J → ℕ)
    (hd : ∀ j, Section1.degree (Section1.ofConjClassFunction (μ j)) = (d j : ℂ))
    (hdpos : ∀ j, 0 < d j) :
    Section1.IsIntegralIsometryOnCharacterDifferences
      (fun j => Section1.ofConjClassFunction (μ j)) d s.localClass
      (Section1.inducedCF (Normalizer P)) :=
  Section1.induction_integralIsometry_of_specialSupport (Normalizer P) (specialSupport P)
    (specialSupport_transporters hP) μ hμ d hd hdpos s.localClass s.localClass_basis
    (fun i => (s.degree i).trans (s.degree 0).symm)
    (fun i => s.difference_supported i 0)

/-- Four distinct ambient irreducibles with a common positive natural degree.
Their signed differences are exactly the induced local differences. -/
structure AmbientRows (s : Rows P) where
  chi : Fin 4 → ConjClassFunction G
  irreducible : ∀ i, IsIrreducibleConjCharacter (chi i)
  distinct : Function.Injective chi
  commonDegree : ℕ
  degree_pos : 0 < commonDegree
  degree : ∀ i, chi i (ConjClasses.mk 1) = (commonDegree : ℂ)
  sign : ℂ
  sign_unit : Section1.IsSign sign
  difference : ∀ i j, inducedClassFunction (Normalizer P) (s.localClass i - s.localClass j) =
    sign • (ofConjClassFunction (chi i) - ofConjClassFunction (chi j))

/-- Extract the ambient exceptional rows by the special-support isometry and
Peterfalvi (1.4). -/
theorem Rows.nonempty_ambientRows (s : Rows P) (hP : Nat.card P = 13) :
    Nonempty (AmbientRows s) := by
  have hd (i : Fin 4) : Section1.degree (s.localClass i) =
      Section1.degree (s.localClass 0) := (s.degree i).trans (s.degree 0).symm
  obtain ⟨ε,hε,μ,hμ,hdeg,he⟩ := Section1.exists_irreducibles_of_specialSupport
    (by decide : 2 ≤ 4) (Normalizer P) (specialSupport P)
    (specialSupport_transporters hP) s.localClass s.localClass_basis hd
    (fun i => s.difference_supported i 0)
  have hc (i) : Section1.IsClassFunction (μ i) :=
    Section1.isBookIrreducibleCharacter_isClassFunction _
      (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup (hμ.1 i))
  let ν := fun i => Section1.toConjClassFunction (μ i) (hc i)
  have hv (i) (g : G) : ν i (ConjClasses.mk g) = μ i g :=
    Section1.toConjClassFunction_apply _ _ _
  obtain ⟨d,ρ,hρ,hchar⟩ := hμ.1 0
  have hd0 : Section1.degree (μ 0) = (d : ℂ) := by
    rw [hchar, Section1.degree_representation_character]
    simp
  refine ⟨{
    chi := ν
    irreducible := fun i =>
      Section1.toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        (hc i) (hμ.1 i)
    distinct := ?_
    commonDegree := d
    degree_pos := ?_
    degree := ?_
    sign := ε
    sign_unit := hε
    difference := ?_ }⟩
  · intro i j hij
    by_contra hne
    apply hμ.2 hne
    funext g
    exact (hv i g).symm.trans ((congrFun hij (ConjClasses.mk g)).trans (hv j g))
  · have hne := Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup _ (hμ.1 0)
    rw [hd0] at hne
    have : d ≠ 0 := by exact_mod_cast hne
    omega
  · intro i
    exact (hv i 1).trans ((hdeg i).trans hd0)
  · intro i j
    have he' (k) : inducedClassFunction (Normalizer P) (s.localClass k - s.localClass 0) =
        ε • (μ k - μ 0) := by
      rw [← Section1.inducedCF_eq_standardInduction]
      exact he k
    have hind : inducedClassFunction (Normalizer P) (s.localClass i - s.localClass j) =
        inducedClassFunction (Normalizer P) (s.localClass i - s.localClass 0) -
        inducedClassFunction (Normalizer P) (s.localClass j - s.localClass 0) := by
      ext g
      unfold inducedClassFunction
      simp only [Pi.sub_apply]
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      split <;> simp
    rw [hind, he' i, he' j]
    ext g
    change ε * (μ i g - μ 0 g) - ε * (μ j g - μ 0 g) =
      ε * (ν i (ConjClasses.mk g) - ν j (ConjClasses.mk g))
    rw [hv, hv]
    ring

/-- The induced differences agree with their local values on P minus one. -/
theorem AmbientRows.restriction_difference {s : Rows P} (t : AmbientRows s)
    (hP : Nat.card P = 13) (i j : Fin 4) (p : P) (hp : p ≠ 1) :
    t.sign * (t.chi i (ConjClasses.mk (p : G)) - t.chi j (ConjClasses.mk (p : G))) =
      s.chi i (ConjClasses.mk (inclusion P p)) - s.chi j (ConjClasses.mk (inclusion P p)) := by
  have hc : IsClassFunction (s.localClass i - s.localClass j) := by
    intro x g
    change ofConjClassFunction (s.chi i) (g*x*g⁻¹) -
      ofConjClassFunction (s.chi j) (g*x*g⁻¹) = _
    rw [ofConjClassFunction_isClassFunction, ofConjClassFunction_isClassFunction]
    rfl
  have ha : inclusion P p ∈ specialSupport P := by
    refine ⟨p.property, ?_⟩
    intro h
    exact hp (Subtype.ext (congrArg (fun x : Normalizer P => (x : G)) h))
  have he := inducedClassFunction_eq_on_specialSupport (Normalizer P) (specialSupport P)
    (specialSupport_transporters hP) _ hc (s.difference_supported i j) (inclusion P p) ha
  rw [t.difference] at he
  exact he

/-- Place the extracted rows into any supplied complete ambient character family. -/
theorem AmbientRows.exists_embedding {s : Rows P} (t : AmbientRows s)
    {J : Type*} [Fintype J] {χ : J → ConjClassFunction G}
    (hχ : IsCompleteIrreducibleCharacterFamily χ) :
    ∃ e : Fin 4 ↪ J, ∀ i, χ (e i) = t.chi i := by
  classical
  have hex (i) := hχ.2.1 (t.chi i) (t.irreducible i)
  choose f hf using hex
  refine ⟨⟨f, ?_⟩, hf⟩
  intro i j hij
  apply t.distinct
  rw [← hf i, ← hf j, hij]

/-- Constructor from the original normalizer hypotheses. -/
theorem nonempty_local_and_ambientRows (P : Subgroup G) (hP : Nat.card P = 13)
    (hC : Subgroup.centralizer (P : Set G) = P)
    (hindex : P.relIndex (Normalizer P) = 3) :
    ∃ s : Rows P, Nonempty (AmbientRows s) := by
  obtain ⟨s⟩ := nonempty_rows P hP hC hindex
  exact ⟨s, s.nonempty_ambientRows hP⟩
end CyclicThirteenNormalizer
