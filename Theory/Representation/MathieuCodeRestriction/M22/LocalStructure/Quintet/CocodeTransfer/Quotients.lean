module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.Spaces
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Geometry
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The compatible quintet pair quotient

The tetrad line is disjoint from the distinguished pair line, so its image
in the ten-dimensional cocode is a nonzero line. The third isomorphism theorem
identifies the quotient by the geometric middle space with the original M24
top section, and the identification intertwines the literal Q action.

The common subgroup is the intersection of the intrinsic octad and sextet
two-cores for the compatible geometry. If its ambient fixed space has dimension
six and its intersection with U7 has dimension five, a fixed vector outside
U7 survives outside V6. These numerical premises are consequences of the
preceding M24 results; they are kept explicit here. The geometric image line
is called W1 until it has been identified with the intrinsic fixed space V1.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
H.15.4, printed p.400, using H.15.2(5) and H.15.3.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
noncomputable section
namespace MathieuCode.M22Quintet.CocodeTransfer

def U1 : Submodule (ZMod 2) Cocode := sextetTetradLine m22SourceSextet

def W1 : Submodule (ZMod 2) M22Cocode := U1.map m22PairLine.mkQ

def QToSextet : Q →* sextetStabilizer m22SourceSextet where
  toFun g := ⟨g.val.val, g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem U1_le_U7 : U1 ≤ U7 := by
  apply Submodule.span_le.mpr
  rw [Set.singleton_subset_iff]
  rw [sextetVector_eq m22SourceSextet m22SourceTetrad_mem]
  have hle : supportedPairSpace (m22SourceTetrad 0) ≤ U7 :=
    le_iSup_of_le (m22SourceTetrad 0) (le_iSup_of_le m22SourceTetrad_mem le_rfl)
  exact hle (tetradVector_mem_supportedPairSpace (by decide +kernel))

theorem pairClass_not_mem_U1 : m22PairClass ∉ U1 := by
  have he : m22PairClass = pairVector ⟨m22Pair, by decide +kernel⟩ := by
    apply congrArg codeInCore.mkQ
    exact Subtype.ext m22PairWord_eq_wordOfSet
  rw [he]
  exact pairVector_not_mem_sextetTetradLine _ _

theorem U1_disjoint_pairLine : Disjoint U1 m22PairLine := by
  apply Submodule.disjoint_def.mpr
  intro u hu hp
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hp
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · exact zero_smul _ _
  · simp only [one_smul] at hu
    exact (pairClass_not_mem_U1 hu).elim

theorem W1_eq_span : W1 = Submodule.span (ZMod 2)
    {m22PairLine.mkQ (sextetVector m22SourceSextet)} := by
  simp only [W1, U1, sextetTetradLine, Submodule.map_span, Set.image_singleton]

theorem tetrad_image_ne_zero :
    m22PairLine.mkQ (sextetVector m22SourceSextet) ≠ 0 := by
  intro hz
  have hm := (Submodule.Quotient.mk_eq_zero m22PairLine).mp hz
  have he := (Submodule.disjoint_def.mp U1_disjoint_pairLine)
    (sextetVector m22SourceSextet) (Submodule.mem_span_singleton_self _) hm
  exact sextetVector_ne_zero _ he

theorem finrank_W1 : Module.finrank (ZMod 2) W1 = 1 := by
  rw [W1_eq_span]
  exact finrank_span_singleton tetrad_image_ne_zero

theorem W1_le_V6 : W1 ≤ V6 := Submodule.map_mono U1_le_U7

theorem U1_fixed (g : Q) (u : Cocode) (hu : u ∈ U1) :
    cocodeRepresentation g.val.val u = u :=
  sextetTetradLine_le_fixed _ hu (QToSextet g)

theorem W1_fixed (g : Q) (v : M22Cocode) (hv : v ∈ W1) :
    m22OuterCocodeRepresentation g.val v = v := by
  obtain ⟨u, hu, rfl⟩ := hv
  rw [m22OuterCocodeRepresentation_mk, U1_fixed g u hu]

def U7Subrepresentation :
    Subrepresentation (cocodeRepresentation.comp (m22PairStabilizer.subtype.comp Q.subtype)) where
  toSubmodule := U7
  apply_mem_toSubmodule := U7_invariant

def W1Subrepresentation :
    Subrepresentation (m22OuterCocodeRepresentation.comp Q.subtype) where
  toSubmodule := W1
  apply_mem_toSubmodule g v hv := by
    change m22OuterCocodeRepresentation g.val v ∈ W1
    rw [W1_fixed g v hv]
    exact hv

/-- The third isomorphism theorem for the actual nested cocode quotients. -/
def topQuotientEquiv : (M22Cocode ⧸ V6) ≃ₗ[ZMod 2] (Cocode ⧸ U7) :=
  Submodule.quotientQuotientEquivQuotient m22PairLine U7 pairLine_le_U7

@[simp] theorem topQuotientEquiv_mk (u : Cocode) :
    topQuotientEquiv (V6.mkQ (m22PairLine.mkQ u)) = U7.mkQ u := rfl

theorem topQuotientEquiv_equivariant (g : Q) (v : M22Cocode ⧸ V6) :
    topQuotientEquiv (V6Subrepresentation.quotientRepresentation g v) =
      U7Subrepresentation.quotientRepresentation g (topQuotientEquiv v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    induction v using Submodule.Quotient.induction_on with
    | _ u => rfl

theorem finrank_topQuotient (hU7 : Module.finrank (ZMod 2) U7 = 7) :
    Module.finrank (ZMod 2) (M22Cocode ⧸ V6) = 4 := by
  have h := V6.finrank_quotient_add_finrank
  rw [finrank_V6_of_U7 hU7, finrank_m22Cocode] at h
  omega

/-- The preimage of the middle term is precisely the original middle term. -/
theorem mk_mem_V6_iff (u : Cocode) : m22PairLine.mkQ u ∈ V6 ↔ u ∈ U7 := by
  change u ∈ (U7.map m22PairLine.mkQ).comap m22PairLine.mkQ ↔ _
  rw [Submodule.comap_map_mkQ, sup_eq_right.mpr pairLine_le_U7]

/-- The quotient does not lose a fixed vector outside the middle term. -/
theorem fixed_vector_survives {A : Subgroup m22PairStabilizer} {u : Cocode}
    (hu : u ∈ fixedSpace (cocodeRepresentation.comp m22PairStabilizer.subtype) A)
    (hout : u ∉ U7) :
    m22PairLine.mkQ u ∈ fixedSpace m22OuterCocodeRepresentation A ∧
      m22PairLine.mkQ u ∉ V6 := by
  refine ⟨fun a => congrArg m22PairLine.mkQ (hu a), ?_⟩
  exact fun h => hout ((mk_mem_V6_iff u).mp h)

/-- The intrinsic M24 kernels for the compatible sextet and octad. -/
def KS : Subgroup M24 :=
  (pCore 2 (sextetStabilizer m22SourceSextet)).map
    (sextetStabilizer m22SourceSextet).subtype

def KO : Subgroup M24 :=
  (pCore 2 (octadStabilizer m22SourceOctad)).map
    (octadStabilizer m22SourceOctad).subtype

/-- The actual common subgroup before, and after, restriction to the pair group. -/
def E24 : Subgroup M24 := KO ⊓ KS

def E : Subgroup m22PairStabilizer := E24.comap m22PairStabilizer.subtype

theorem E_map_eq (hE : E24 ≤ m22PairStabilizer) :
    E.map m22PairStabilizer.subtype = E24 := by
  ext g
  constructor
  · rintro ⟨e, he, rfl⟩
    exact he
  · intro hg
    exact ⟨⟨g, hE hg⟩, hg, rfl⟩

/-- Normality is relative to Q, as required by the source. -/
theorem Q_le_normalizer_K : Q ≤ Subgroup.normalizer (K : Set m22PairStabilizer) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg k hk
  obtain ⟨a, ha, rfl⟩ := hk
  exact ⟨(⟨g,hg⟩ : Q) * a * (⟨g,hg⟩ : Q)⁻¹,
    (inferInstance : (pCore 2 Q).Normal).conj_mem a ha ⟨g,hg⟩, rfl⟩

/-- H.15.2(5) gives six fixed dimensions in the ambient cocode. H.15.3(2)
gives five in U7. Their difference survives the literal pair quotient. -/
theorem common_fixedSpace_not_le_V6
    (hfixed : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation E24) = 6)
    (hmiddle : Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation E24 ⊓ U7 : Submodule (ZMod 2) Cocode) = 5) :
    ¬ fixedSpace m22OuterCocodeRepresentation E ≤ V6 := by
  have hout : ¬ fixedSpace cocodeRepresentation E24 ≤ U7 := by
    intro h
    rw [inf_eq_left.mpr h, hfixed] at hmiddle
    omega
  obtain ⟨u, hu, huout⟩ := SetLike.not_le_iff_exists.mp hout
  have hfix : u ∈ fixedSpace
      (cocodeRepresentation.comp m22PairStabilizer.subtype) E := by
    intro e
    exact hu ⟨e.val.val, e.property⟩
  obtain ⟨hv, hvout⟩ := fixed_vector_survives hfix huout
  exact fun h => hvout (h hv)

/-- A transvection displacement in the M24 tetrad line descends to its image. -/
theorem displacement_mem_W1 (k : m22PairStabilizer)
    (hmove : ∀ u ∈ U7, cocodeRepresentation k.val u - u ∈ U1)
    (v : M22Cocode) (hv : v ∈ V6) :
    m22OuterCocodeRepresentation k v - v ∈ W1 := by
  obtain ⟨u, hu, rfl⟩ := hv
  exact ⟨cocodeRepresentation k.val u - u, hmove u hu, map_sub _ _ _⟩

end MathieuCode.M22Quintet.CocodeTransfer
