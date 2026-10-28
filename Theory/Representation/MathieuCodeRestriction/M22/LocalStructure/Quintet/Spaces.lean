module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Pairing
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.DualCommutator

/-!
# Geometric spaces for the outer M22 quintet

The cocode middle term is the image of the pair-generated space of the
compatible sextet under the literal quotient by the distinguished pair line.
The code terms are its annihilator and the annihilators of the two intrinsic
cocode fixed spaces, using the coordinate pairing. These constructions assume
no chief-factor, fixed-dimension, or transvection conclusions.

The pair line lies in the geometric space, so quotienting lowers its dimension
by one. Annihilation reverses inclusions and complements dimensions. Invariance
is proved for the geometric term and transported through the actual pairing.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
H.15.4 and H.16.3, printed pp.400,403.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
open scoped Pointwise
namespace MathieuCode.M22Quintet

abbrev Q := m22OuterQuintetStabilizer m22SourceSextet
abbrev K := m22OuterQuintetKernel m22SourceSextet

/-- The native inner group as an actual subgroup of the setwise pair group. -/
def L : Subgroup m22PairStabilizer := m22ToPairStabilizer.range

/-- The two fixed spaces appearing in H.15.4(1). -/
def V1 : Submodule (ZMod 2) M22Cocode := fixedSpace m22OuterCocodeRepresentation K
def V2 : Submodule (ZMod 2) M22Cocode := fixedSpace m22OuterCocodeRepresentation (K ⊓ L)

/-- The pair-generated space in the eleven-dimensional cocode, before quotienting. -/
def U7 : Submodule (ZMod 2) Cocode :=
  ⨆ B ∈ m22SourceSextet.parts, supportedPairSpace B

/-- The geometric middle term in the literal ten-dimensional quotient. -/
def V6 : Submodule (ZMod 2) M22Cocode := U7.map m22PairLine.mkQ

theorem V1_le_V2 : V1 ≤ V2 := by
  intro v hv g
  exact hv ⟨g.val, g.property.1⟩

theorem pairLine_le_U7 : m22PairLine ≤ U7 := by
  apply Submodule.span_le.mpr
  rintro v (rfl : v = m22PairClass)
  have hle : supportedPairSpace (m22SourceTetrad 0) ≤ U7 :=
    le_iSup_of_le (m22SourceTetrad 0) (le_iSup_of_le m22SourceTetrad_mem le_rfl)
  apply hle
  have he : m22PairClass = pairVector ⟨m22Pair, by decide +kernel⟩ := by
    apply congrArg codeInCore.mkQ
    exact Subtype.ext m22PairWord_eq_wordOfSet
  rw [he]
  exact pairVector_mem_supportedPairSpace _ m22Pair_le_sourceTetrad

/-- The actual quotient map loses precisely the distinguished pair line. -/
theorem finrank_V6_add_one :
    Module.finrank (ZMod 2) V6 + 1 = Module.finrank (ZMod 2) U7 := by
  let f : U7 →ₗ[ZMod 2] M22Cocode := m22PairLine.mkQ.comp U7.subtype
  have hr : LinearMap.range f = V6 := by
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  have hk : LinearMap.ker f = m22PairLine.comap U7.subtype := by
    ext u
    exact Submodule.Quotient.mk_eq_zero m22PairLine
  have h := f.finrank_range_add_finrank_ker
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe pairLine_le_U7).finrank_eq,
    finrank_m22PairLine] at h
  exact h

theorem finrank_V6_of_U7 (hU : Module.finrank (ZMod 2) U7 = 7) :
    Module.finrank (ZMod 2) V6 = 6 := by
  have h := finrank_V6_add_one
  omega

private theorem supportedPairSpace_invariant (g : M24) (B : Finset (Fin 24))
    (v : Cocode) (hv : v ∈ supportedPairSpace B) :
    cocodeRepresentation g v ∈ supportedPairSpace (g • B) := by
  have hle : supportedPairSpace B ≤
      (supportedPairSpace (g • B)).comap (cocodeRepresentation g) := by
    apply Submodule.span_le.mpr
    rintro w ⟨P, hP, rfl⟩
    change cocodeRepresentation g (pairVector P) ∈ supportedPairSpace (g • B)
    rw [pairVector_equivariant]
    apply pairVector_mem_supportedPairSpace
    exact Finset.smul_finset_subset_smul_finset hP
  exact hle hv

theorem U7_invariant (g : Q) (u : Cocode) (hu : u ∈ U7) :
    cocodeRepresentation g.val.val u ∈ U7 := by
  have hle : U7 ≤ U7.comap (cocodeRepresentation g.val.val) := by
    refine iSup_le fun B => iSup_le fun hB => ?_
    intro v hv
    change cocodeRepresentation g.val.val v ∈ U7
    have hS : g.val.val • m22SourceSextet.parts = m22SourceSextet.parts :=
      MulAction.mem_stabilizer_iff.mp g.property
    have hB' : g.val.val • B ∈ m22SourceSextet.parts := by
      rw [← hS]
      exact Finset.smul_mem_smul_finset hB
    have hB'' : supportedPairSpace (g.val.val • B) ≤ U7 :=
      le_iSup_of_le (g.val.val • B) (le_iSup_of_le hB' le_rfl)
    exact hB'' (supportedPairSpace_invariant g.val.val B v hv)
  exact hle hu

theorem V6_invariant (g : Q) (v : M22Cocode) (hv : v ∈ V6) :
    m22OuterCocodeRepresentation g.val v ∈ V6 := by
  obtain ⟨u, hu, rfl⟩ := hv
  exact ⟨cocodeRepresentation g.val.val u, U7_invariant g u hu, rfl⟩

def V6Subrepresentation :
    Subrepresentation (m22OuterCocodeRepresentation.comp Q.subtype) where
  toSubmodule := V6
  apply_mem_toSubmodule := V6_invariant

/-- Annihilation uses the existing coordinate duality, not a choice of basis. -/
def annihilator (U : Submodule (ZMod 2) M22Cocode) : Submodule (ZMod 2) M22Code :=
  U.dualAnnihilator.comap m22CodeCocodeDuality.toLinearMap

theorem mem_annihilator (U : Submodule (ZMod 2) M22Cocode) (v : M22Code) :
    v ∈ annihilator U ↔ ∀ u ∈ U, m22CodeCocodeDuality v u = 0 :=
  Submodule.mem_dualAnnihilator (m22CodeCocodeDuality v)

theorem annihilator_antitone {U W : Submodule (ZMod 2) M22Cocode} (h : U ≤ W) :
    annihilator W ≤ annihilator U :=
  Submodule.comap_mono (Submodule.dualAnnihilator_anti h)

theorem finrank_annihilator_add (U : Submodule (ZMod 2) M22Cocode) :
    Module.finrank (ZMod 2) (annihilator U) + Module.finrank (ZMod 2) U = 10 := by
  unfold annihilator
  rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq, add_comm,
    Subspace.finrank_add_finrank_dualAnnihilator_eq, finrank_m22Cocode]

theorem annihilator_invariant (U : Submodule (ZMod 2) M22Cocode)
    (hU : ∀ g : Q, ∀ u ∈ U, m22OuterCocodeRepresentation g.val u ∈ U)
    (g : Q) (v : M22Code) (hv : v ∈ annihilator U) :
    m22OuterCodeRepresentation g.val v ∈ annihilator U := by
  rw [mem_annihilator] at hv ⊢
  intro u hu
  rw [m22CodeCocodeDuality_equivariant]
  exact hv _ (hU g⁻¹ u hu)

/-- The annihilator is genuinely the dual of the quotient, by the coordinate pairing. -/
def annihilatorQuotientDuality (U : Submodule (ZMod 2) M22Cocode) :
    annihilator U ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (M22Cocode ⧸ U) :=
  (m22CodeCocodeDuality.ofSubmodule' U.dualAnnihilator).trans
    U.dualQuotEquivDualAnnihilator.symm

@[simp] theorem annihilatorQuotientDuality_mk (U : Submodule (ZMod 2) M22Cocode)
    (v : annihilator U) (u : M22Cocode) :
    annihilatorQuotientDuality U v (U.mkQ u) = m22CodeCocodeDuality v.val u := rfl

def annihilatorSubrepresentation
    (U : Subrepresentation (m22OuterCocodeRepresentation.comp Q.subtype)) :
    Subrepresentation (m22OuterCodeRepresentation.comp Q.subtype) where
  toSubmodule := annihilator U.toSubmodule
  apply_mem_toSubmodule := annihilator_invariant U.toSubmodule
    (fun g _ hu => U.apply_mem_toSubmodule g hu)

/-- The quotient duality intertwines the actual restricted actions. -/
theorem annihilatorQuotientDuality_equivariant
    (U : Subrepresentation (m22OuterCocodeRepresentation.comp Q.subtype))
    (g : Q) (v : annihilator U.toSubmodule) :
    annihilatorQuotientDuality U.toSubmodule
        ((annihilatorSubrepresentation U).toRepresentation g v) =
      U.quotientRepresentation.dual g (annihilatorQuotientDuality U.toSubmodule v) := by
  apply LinearMap.ext
  intro u
  induction u using Submodule.Quotient.induction_on with
  | _ u =>
    change m22CodeCocodeDuality (m22OuterCodeRepresentation g.val v.val) u =
      m22CodeCocodeDuality v.val (m22OuterCocodeRepresentation g.val⁻¹ u)
    exact LinearMap.congr_fun (m22CodeCocodeDuality_equivariant g.val v.val) u

/-- Pointwise fixation of the annihilator is equivalent to trivial action on
the cocode quotient. No maximality or faithfulness is hidden in this equivalence. -/
theorem fixes_annihilator_iff (U : Submodule (ZMod 2) M22Cocode)
    (g : m22PairStabilizer) :
    (∀ v ∈ annihilator U, m22OuterCodeRepresentation g v = v) ↔
      ∀ u, m22OuterCocodeRepresentation g u - u ∈ U := by
  constructor
  · intro hfix u
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U _).mp
    intro f hf
    obtain ⟨v, rfl⟩ := m22CodeCocodeDuality.surjective f
    have hv : v ∈ annihilator U := hf
    have he := m22CodeToCocodeDual_invariant g v u
    rw [hfix v hv] at he
    exact (map_sub _ _ _).trans (sub_eq_zero.mpr (by simpa only [m22CodeCocodeDuality_apply] using he))
  · intro hmove v hv
    apply m22CodeCocodeDuality.injective
    apply LinearMap.ext
    intro u
    rw [m22CodeCocodeDuality_equivariant]
    change m22CodeCocodeDuality v (m22OuterCocodeRepresentation g⁻¹ u) =
      m22CodeCocodeDuality v u
    have he := (mem_annihilator U v).mp hv _
      (hmove (m22OuterCocodeRepresentation g⁻¹ u))
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, map_sub, sub_eq_zero] at he
    exact he.symm

/-- Fixed code vectors are the annihilator of the actual cocode commutator space. -/
theorem code_fixedSpace_eq_annihilator_commutator (A : Subgroup m22PairStabilizer) :
    fixedSpace m22OuterCodeRepresentation A =
      annihilator (Representation.Coinvariants.ker
        (m22OuterCocodeRepresentation.comp A.subtype)) := by
  unfold annihilator
  rw [← Representation.invariants_dual_eq_commutator_annihilator]
  ext v
  change (∀ g : A, m22OuterCodeRepresentation g.val v = v) ↔
    ∀ g : A, Representation.dual (m22OuterCocodeRepresentation.comp A.subtype) g
      (m22CodeCocodeDuality v) = m22CodeCocodeDuality v
  constructor
  · intro hv g
    exact (m22CodeCocodeDuality_equivariant g.val v).symm.trans
      (congrArg m22CodeCocodeDuality (hv g))
  · intro hv g
    apply m22CodeCocodeDuality.injective
    exact (m22CodeCocodeDuality_equivariant g.val v).trans (hv g)

def V4 : Submodule (ZMod 2) M22Code := annihilator V6
def V8 : Submodule (ZMod 2) M22Code := annihilator V2
def V9 : Submodule (ZMod 2) M22Code := annihilator V1

theorem V8_le_V9 : V8 ≤ V9 := annihilator_antitone V1_le_V2

theorem V4_invariant (g : Q) (v : M22Code) (hv : v ∈ V4) :
    m22OuterCodeRepresentation g.val v ∈ V4 :=
  annihilator_invariant V6 V6_invariant g v hv

def V4Subrepresentation :
    Subrepresentation (m22OuterCodeRepresentation.comp Q.subtype) where
  toSubmodule := V4
  apply_mem_toSubmodule := V4_invariant

/-- The dimensions of the dual terms follow from the three cocode dimensions.
The cocode dimensions are still premises here, not assertions of H.15.4. -/
theorem code_flag_dimensions
    (h1 : Module.finrank (ZMod 2) V1 = 1)
    (h2 : Module.finrank (ZMod 2) V2 = 2)
    (h6 : Module.finrank (ZMod 2) V6 = 6) :
    Module.finrank (ZMod 2) V4 = 4 ∧
    Module.finrank (ZMod 2) V8 = 8 ∧ Module.finrank (ZMod 2) V9 = 9 := by
  have h4 := finrank_annihilator_add V6
  have h8 := finrank_annihilator_add V2
  have h9 := finrank_annihilator_add V1
  change Module.finrank (ZMod 2) V4 + _ = 10 at h4
  change Module.finrank (ZMod 2) V8 + _ = 10 at h8
  change Module.finrank (ZMod 2) V9 + _ = 10 at h9
  omega

/-- Strictness of the dual flag follows from containment and the cocode
dimensions. Irreducibility of the successive sections remains a separate fact. -/
theorem code_flag_strict (h26 : V2 ≤ V6)
    (h1 : Module.finrank (ZMod 2) V1 = 1)
    (h2 : Module.finrank (ZMod 2) V2 = 2)
    (h6 : Module.finrank (ZMod 2) V6 = 6) :
    (⊥ : Submodule (ZMod 2) M22Code) < V4 ∧ V4 < V8 ∧ V8 < V9 ∧ V9 < ⊤ := by
  obtain ⟨h4, h8, h9⟩ := code_flag_dimensions h1 h2 h6
  refine ⟨lt_of_le_of_ne bot_le ?_, lt_of_le_of_ne (annihilator_antitone h26) ?_,
    lt_of_le_of_ne V8_le_V9 ?_, lt_of_le_of_ne le_top ?_⟩
  · intro he
    have hd := congrArg (fun W : Submodule (ZMod 2) M22Code => Module.finrank (ZMod 2) W) he
    simp only [finrank_bot, h4] at hd
    omega
  · intro he
    have hd := congrArg (fun W : Submodule (ZMod 2) M22Code => Module.finrank (ZMod 2) W) he
    omega
  · intro he
    have hd := congrArg (fun W : Submodule (ZMod 2) M22Code => Module.finrank (ZMod 2) W) he
    omega
  · intro he
    have hd := congrArg (fun W : Submodule (ZMod 2) M22Code => Module.finrank (ZMod 2) W) he
    simp only [finrank_top, finrank_m22Code, h9] at hd
    omega

theorem V4_eq_fixedSpace_of_commutator
    (hmoved : Representation.Coinvariants.ker
      (m22OuterCocodeRepresentation.comp K.subtype) = V6) :
    V4 = fixedSpace m22OuterCodeRepresentation K := by
  rw [code_fixedSpace_eq_annihilator_commutator, hmoved]
  rfl

end MathieuCode.M22Quintet
