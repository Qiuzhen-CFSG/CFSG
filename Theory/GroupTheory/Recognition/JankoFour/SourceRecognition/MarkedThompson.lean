module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedOverlaps
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.OverlapIndices
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.NoFF
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Thompson subgroups from an actual Mathieu cocode marking

Faithfulness of the cocode action identifies the full ambient centralizer
of the marked elementary subgroup with that subgroup. A maximum elementary
subgroup acting nontrivially would give an FF offender in the same M24
representation. The proved cocode non-FF theorem therefore identifies the
Thompson subgroup of every intermediate subgroup with the original kernel.

For a type-J4 sextet marker the literal point-plane overlap has odd index
77 in its involution centralizer. A Sylow subgroup of that overlap is thus
ambient Sylow. Conjugacy inside the same centralizer aligns the kernel with
the Thompson subgroup of any other Sylow there. MarkedLocalData uses this
alignment to construct native line and incidence data.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), (4.5)--(4.8), pp.598--599, DOI 10.1007/BF01232280.
The non-FF input uses the checked cocode action, as cited in QuadraticActors.NoFF.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G]
variable (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))

omit [Finite G] in
include hk hE in
/-- The literal cocode kernel is self-centralizing in the ambient group. -/
theorem marked_cocode_selfCentralizing : Subgroup.centralizer (W : Set G) = W := by
  apply le_antisymm
  · intro x hx
    let n : normalizer (W : Set G) := ⟨x,Subgroup.centralizer_le_normalizer _ hx⟩
    have hn : f n = 1 := by
      apply cocode_faithful
      rw [map_one]
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := E.surjective v
      change cocodeRepresentation (f n) (E (Additive.ofMul w.toMul)) = E (Additive.ofMul w.toMul)
      rw [←hE n w.toMul]
      apply congrArg E
      apply Additive.ofMul.injective
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hx w.toMul.val w.toMul.property).symm
    have hn0 : n ∈ f.ker := hn
    rw [hk] at hn0
    exact hn0
  · exact le_centralizer_iff_isMulCommutative.mpr inferInstance

include hf hk hE in
/-- A subgroup between the cocode kernel and its normalizer has exactly this Thompson subgroup. -/
theorem marked_cocode_thompson (S : Subgroup G)
    (hWS : W ≤ S) (hSN : S ≤ normalizer (W : Set G)) :
    elementaryAbelianMaxJ S = W := by
  let N := normalizer (W : Set G)
  let W0 := W.subgroupOf N
  let : IsElementaryAbelian 2 W0 := IsElementaryAbelian.subgroupOf W.le_normalizer
  have hc := marked_cocode_selfCentralizing W f hk E hE
  have hker : f.ker = Subgroup.centralizer (W0 : Set N) := by
    rw [hk]
    ext n
    constructor
    · intro hn w hw
      apply Subtype.ext
      exact ((Commute.all (⟨w.val,hw⟩ : W) ⟨n.val,hn⟩).map W.subtype).eq
    · intro hn
      apply hc.le
      intro w hw
      exact congrArg N.subtype (hn ⟨w,W.le_normalizer hw⟩ hw)
  let F : Additive W0 ≃ₗ[ZMod 2] Cocode :=
    ((subgroupOfEquivOfLe W.le_normalizer).toAdditive.toLinearEquiv (ZMod.map_smul _)).trans E
  let τ := NormalElementaryQuotient.representation W0 f hf hker
  have hF (a : M24) (v : Additive W0) : F (τ a v) = cocodeRepresentation a (F v) := by
    obtain ⟨n,rfl⟩ := hf a
    have he := NormalElementaryQuotient.representation_apply W0 f hf hker n v
    have hev : (subgroupOfEquivOfLe W.le_normalizer) (τ (f n) v).toMul =
        W.normalizerMonoidHom n ((subgroupOfEquivOfLe W.le_normalizer) v.toMul) := by
      apply Subtype.ext
      exact congrArg N.subtype he
    change E (Additive.ofMul ((subgroupOfEquivOfLe W.le_normalizer) (τ (f n) v).toMul)) = _
    rw [hev,hE]
    rfl
  have hJ : elementaryAbelianMaxJ (S.subgroupOf N) ≤ f.ker := by
    by_contra hn
    have hh := NormalElementaryQuotient.isFFModule_of_thompson_not_le W0 f hf hker
      (S.subgroupOf N) (comap_mono hWS) hn
    exact QuadraticActors.cocode_not_isFFModule
      (hh.map_equivariant τ cocodeRepresentation (MonoidHom.id M24) (fun _ _ he => he) F hF)
  have hJW : elementaryAbelianMaxJ S ≤ W := by
    rw [←map_subgroupOf_eq_of_le hSN,elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective]
    rintro _ ⟨n,hn,rfl⟩
    have hn0 := hJ hn
    rw [hk] at hn0
    exact hn0
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
  have hAW : A = W := eq_of_le_of_card_ge ((le_sSup hA).trans hJW)
    (hA.2.2 W hWS inferInstance)
  exact le_antisymm hJW (hAW ▸ le_sSup hA)

include hf hk hE in
/-- The sextet overlap supplies an ambient Sylow with the original cocode kernel as its Thompson subgroup. -/
theorem marked_cocode_sylow (z : W) (S : M24LocalGeometry.Sextet)
    (hz : E (Additive.ofMul z) = sextetVector S)
    (h : IsTypeJ4 (z : G)) :
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ centralizer (z : G) ⊓ normalizer (W : Set G) ∧
      elementaryAbelianMaxJ (T : Subgroup G) = W := by
  let N := normalizer (W : Set G)
  let C := centralizer (z : G)
  let B := N.subgroupOf C
  have hcard : Nat.card W = 2048 := by
    change Nat.card (Additive W) = _
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_cocode,Nat.card_zmod]
    norm_num
  have hplane := marked_cocode_plane_card W f hf hk hcard E hE z S hz
  have hi : B.index = 77 := marked_pointPlane_plane_index h N hplane
  let P : Sylow 2 B := Sylow.nonempty.some
  let V : Subgroup C := (P : Subgroup B).map B.subtype
  have hp : IsPGroup 2 V := P.isPGroup'.map B.subtype
  have hvi : V.index = P.index * 77 := by
    rw [Subgroup.index_map_of_injective _ B.subtype_injective,range_subtype,hi]
  let Q : Sylow 2 C := hp.toSylow (by
    rw [hvi]
    exact Nat.Prime.not_dvd_mul (by decide) P.not_dvd_index (by decide))
  obtain ⟨T,hT⟩ := h.exists_ambient_sylow Q
  have hTN : (T : Subgroup G) ≤ N := by
    rw [hT]
    rintro _ ⟨q,⟨p,hp,rfl⟩,rfl⟩
    exact p.property
  have hTC : (T : Subgroup G) ≤ C := hT ▸ map_subtype_le _
  have hW0 : IsPGroup 2 (W.subgroupOf N) :=
    (IsElementaryAbelian.isPGroup 2 W).comap_subtype
  have hWT : W ≤ (T : Subgroup G) := by
    have hh := hW0.le_sylow_of_normal (T.subtype hTN)
    intro w hw
    exact hh (show (⟨w,W.le_normalizer hw⟩ : N) ∈ W.subgroupOf N from hw)
  exact ⟨T,le_inf hTC hTN,marked_cocode_thompson W f hf hk E hE _ hWT hTN⟩

include hf hk hE in
/-- An actual marker-centralizing conjugator aligns the kernel with any compatible Sylow. -/
theorem marked_cocode_common_thompson (z : W) (S : M24LocalGeometry.Sextet)
    (hz : E (Additive.ofMul z) = sextetVector S)
    (h : IsTypeJ4 (z : G)) (U : Sylow 2 G)
    (hUC : (U : Subgroup G) ≤ centralizer (z : G)) :
    ∃ g : centralizer (z : G), W.map (MulAut.conj (g : G)).toMonoidHom =
      elementaryAbelianMaxJ (U : Subgroup G) := by
  obtain ⟨T,hT,hJ⟩ := marked_cocode_sylow W f hf hk E hE z S hz h
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (centralizer (z : G))
    (T.subtype (hT.trans inf_le_left)) (U.subtype hUC)
  rw [Sylow.smul_subtype] at hg
  have he := congrArg Sylow.toSubgroup (Sylow.subtype_injective hg)
  refine ⟨g,?_⟩
  exact (congrArg (fun A : Subgroup G => A.map (MulAut.conj (g : G)).toMonoidHom) hJ.symm).trans
    ((elementaryAbelianMaxJ_map_equiv _ _).symm.trans (congrArg elementaryAbelianMaxJ he))

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
