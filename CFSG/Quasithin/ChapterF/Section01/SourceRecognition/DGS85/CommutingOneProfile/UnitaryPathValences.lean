module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBinaryBetaPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryPathProfile

/-!
# Actual unitary neighbor counts

The point stabilizer inside each source local group is the normalizer of
its marked Sylow two-subgroup. Quotienting by the local two-core and
matching the matrix Borel gives the actual neighbor counts q_alpha+1 and
q_beta cubed plus one. The special unitary calculation pulls the Sylow
normalizer through the central projection; it does not replace the Sylow
by its full inverse image. Every positive fixed-field degree is included.

The final theorem transports both local quotient markings through the
literal original inclusion and counts both vertex orbits. UnitaryPathParameters
uses these counts with the proved whole-core order and odd five-walk fixers.
Source: DGS85, Groups and Graphs (1985), (6.1), (11.8)(b,c,g),
printed pp.122,175--177; Huppert II.10.12 for the isotropic-point action.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem source_neighbor_card_of_normalizer_index (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    {D₀ : Type*} [Group D₀]
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* D₀)
    (N : ℕ) (hN₀ : ∀ T : Sylow 2 D₀, (normalizer (T : Set D₀)).index = N) :
    Nat.card ((graph (family P)).neighborSet b) = N := by
  let := finite_endpoints h
  let D := d.localGroup b
  let : Finite D := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
  let q := eb.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hq : Function.Surjective q := eb.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 D := by
    rw [MonoidHom.ker_comp_of_injective _ _ eb.injective,QuotientGroup.ker_mk']
  let R := T.mapSurjective hq
  have hRT : (R : Subgroup D₀).comap q = T := by
    change ((T : Subgroup D).map q).comap q = _
    rw [Subgroup.comap_map_eq,hk,sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)]
  have hN : (normalizer (R : Set D₀)).comap q = normalizer (T : Set D) := by
    change (normalizer ((R : Subgroup D₀) : Set D₀)).comap q = _
    rw [comap_normalizer_eq_of_surjective _ hq,hRT]
    rfl
  have hidx : (normalizer (T : Set D)).index = N := by
    rw [←hN,index_comap_of_surjective _ hq]
    exact hN₀ R
  have he := (source_edge_local_normalizer h d hab.symm Mb T hT).2
  have hstab : MulAction.stabilizer D a = normalizer (T : Set D) := he
  have horbit : MulAction.orbit D a = (graph (family P)).neighborSet b := by
    ext v
    constructor
    · rintro ⟨t,rfl⟩
      have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) (t : G)).map_adj_iff.mpr hab.symm
      change (graph (family P)).Adj ((t : G) • b) ((t : G) • a) at hh
      rwa [show (t : G) • b = b from d.local_le b t.property] at hh
    · intro hv
      obtain ⟨t,ht,hta⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨v,hv⟩
      exact ⟨⟨t,ht⟩,hta⟩
  rw [←horbit,Nat.card_congr (MulAction.orbitEquivQuotientStabilizer D a),
    ←index_eq_card,hstab,hidx]

private theorem projective_unitary_normalizer_index {K : Type*} [Field K] [Finite K]
    (J : HermitianForm 3 K) {m : ℕ} (hm : 0 < m)
    (hc : Nat.card K = (2^m)^2) (hf : ∀ x, J.conj x = x^(2^m))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    (normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J))).index = 2^(3*m)+1 := by
  obtain ⟨C,hC,g,hT⟩ := Unitary.psu_sylow_normalizer_eq_matrix_borel J m hm hc hf T
  obtain ⟨hcard,a,o,ho,ht⟩ := HermitianForm.IsotropicBorelAction.exists_action
    (Unitary.FormTransport.standardForm J) rfl (2^m) hc (Unitary.fixed_card J m hm hc hf)
  let := a
  let := ht
  let := MulAction.isPretransitive_of_is_two_pretransitive
    (G := ProjectiveSpecialUnitaryMatrixGroup (Unitary.FormTransport.standardForm J))
    (α := BenderSuzuki.Converse.psuOmega (Unitary.FormTransport.standardForm J))
  rw [hT,index_comap_of_surjective _ (Unitary.FormTransport.projectiveEquiv J C hC).surjective]
  erw [index_map_equiv (e := MulAut.conj g),←ho,MulAction.index_stabilizer_of_transitive,hcard,←pow_mul]
  congr 2
  omega

/-- Both unitary covers have the same actual local valence. -/
theorem source_unitary_neighbor_card (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m)) :
    Nat.card ((graph (family P)).neighborSet b) = 2^(3*m)+1 := by
  rcases mark with mark | mark
  · have M := IsRankOneModel.projective_unitary m hm mark
    obtain ⟨K,_,_,J,hc,hf,⟨e⟩⟩ := mark
    exact source_neighbor_card_of_normalizer_index h hB d hab M e _
      (projective_unitary_normalizer_index J hm hc hf)
  · have M := IsRankOneModel.special_unitary m hm mark
    obtain ⟨K,_,_,J,hc,hf,⟨e⟩⟩ := mark
    apply source_neighbor_card_of_normalizer_index h hB d hab M e
    intro T
    rw [←T.normalizer_comap_of_central_kernel J.specialToProjective
      J.specialToProjective_surjective J.specialToProjective_ker_le_center,
      index_comap_of_surjective _ J.specialToProjective_surjective]
    exact projective_unitary_normalizer_index J hm hc hf _

variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- Neighbor counts from the literal original quotient markings, with both
unitary covers and every positive fixed-field degree retained. -/
theorem original_reduced_unitary_neighbor_cards
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {m : ℕ} (hm : 0 < m)
    (markα : ClassicalGroup.IsPSL ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)))
    (markβ : ClassicalGroup.IsPSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
      IsSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m))
    (v : Vertex F₀) :
    Nat.card ((graph F₀).neighborSet v) = 2^(if v.type then 3*m else 2*m)+1 := by
  let ea₀ := (d.localGroup (base F₀ false)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea₀ (pCore_map_iso 2 ea₀)
  let eb₀ := (d.localGroup (base F₀ true)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  have markα' := markα.of_mulEquiv eqa
  have markβ' : ClassicalGroup.IsPSU (d.localGroup (base F₀ true) ⧸
      pCore 2 (d.localGroup (base F₀ true))) 3 (2^m) ∨
      IsSU (d.localGroup (base F₀ true) ⧸ pCore 2 (d.localGroup (base F₀ true))) 3 (2^m) := by
    rcases markβ with markβ | ⟨K,_,_,J,hc,hf,⟨eb⟩⟩
    · exact Or.inl (markβ.of_mulEquiv eqb)
    · exact Or.inr ⟨K,inferInstance,inferInstance,J,hc,hf,⟨eqb.trans eb⟩⟩
  have hab : (graph F₀).Adj (base F₀ false) (base F₀ true) :=
    ⟨Bool.false_ne_true,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hβ := source_unitary_neighbor_card (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hab hm markβ'
  have hα : Nat.card ((graph F₀).neighborSet (base F₀ false)) = 2^(2*m)+1 := by
    have M := IsRankOneModel.linear (2*m) (by omega) markα'
    obtain ⟨k,_,_,hk,⟨ea⟩⟩ := markα'
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hk)
    let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
      MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
    have hh := source_linear_neighbor_card (Reduction.reduced_triple h)
      (Reduction.reduced_borel_core_sylow h) d hab.symm M (ea.trans ep.symm)
    change Nat.card ((graph F₀).neighborSet (base F₀ false)) = Nat.card k + 1 at hh
    rwa [hk] at hh
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F₀ v
  have he := Nat.card_congr
    ((Subgroup.CosetGeometry.translationGraphIso F₀ g).mapNeighborSet (base F₀ v.type))
  change Nat.card ((graph F₀).neighborSet (base F₀ v.type)) =
    Nat.card ((graph F₀).neighborSet (g • base F₀ v.type)) at he
  rw [hg] at he
  rw [←he]
  cases v.type
  · exact hα
  · exact hβ

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
