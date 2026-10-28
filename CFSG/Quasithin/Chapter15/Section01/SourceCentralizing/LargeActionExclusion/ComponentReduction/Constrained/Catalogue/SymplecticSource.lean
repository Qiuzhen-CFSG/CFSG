module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SymplecticMembership
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LinearMembership
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedAutomorphism
public import Theory.Representation.SymplecticNaturalNormalizer.Centralizers
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalSeparation

/-!
# Natural symplectic residuals on the original local family

For every eligible K in L(G₁,S), the actual natural symplectic moved section
makes the S-action preserve the two parabolic types. A binary intertwiner
normalizes the natural matrix image; its induced automorphism preserves the
diagram. Normality of the diagram kernel retains this fact under the original
quotient marking and one simultaneous Sylow alignment.

Both literal parabolic residuals therefore belong to L(G₁,S). Their nonshort
rank-one quotients give placement in M_Z by the already proved nonblock
argument, contradicting their generation of K. No ambient C-componenthood,
new CaseIComponentData, or C.2.7 marked-parabolic premise is used for K.
ReducedModels consumes this exclusion to classify the entire local family.

Source: Aschbacher--Smith 15.1.20(2), printed pp.1094--1095, and the
natural symplectic row of B.5.1, pp.99--103.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer

private theorem diagram_of_intertwiner
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (hF : 2 < Nat.card F) (a : MulAut (Sp F))
    (b : Vector F ≃ₗ[ZMod 2] Vector F)
    (hb : ∀ g v, b (symplecticNatural 2 g v) = symplecticNatural 2 (a g) (b v)) :
    PreservesDiagram a := by
  have he (g : Sp F) : b * SymplecticNaturalNormalizer.naturalHom g * b⁻¹ =
      SymplecticNaturalNormalizer.naturalHom (a g) := by
    apply LinearEquiv.ext
    intro v
    change b (symplecticNatural 2 g (b.symm v)) = symplecticNatural 2 (a g) v
    rw [hb,b.apply_symm_apply]
  have hn : b ∈ naturalNormalizer := by
    apply mem_normalizer_iff.mpr
    intro c
    constructor
    · rintro ⟨g,rfl⟩
      change b * SymplecticNaturalNormalizer.naturalHom g.val * b⁻¹ ∈ naturalDerivedImage
      rw [he]
      exact SymplecticNaturalNormalizer.naturalHom_mem hF (a g.val)
    · intro hc
      obtain ⟨g,hg⟩ := hc
      have hx := he (a.symm g.val)
      rw [a.apply_symm_apply] at hx
      have hh : b * SymplecticNaturalNormalizer.naturalHom (a.symm g.val) * b⁻¹ =
          b * c * b⁻¹ := hx.trans hg
      have hcc : c = SymplecticNaturalNormalizer.naturalHom (a.symm g.val) := by
        exact (mul_left_cancel (mul_right_cancel hh)).symm
      rw [hcc]
      exact SymplecticNaturalNormalizer.naturalHom_mem hF _
  have heq := SymplecticNaturalNormalizer.conjugation_eq_of_intertwines hF ⟨b,hn⟩ a hb
  exact heq ▸ SymplecticNaturalNormalizer.conjugation_preservesDiagram hF ⟨b,hn⟩

variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
private theorem moved_symplectic_diagram
    (ρ : Representation (ZMod 2) D W) (L J : Subgroup D) [L.Normal]
    (hLJ : L ≤ J) (s : MovedSection (ρ.comp J.subtype) (L.subgroupOf J))
    (F : BinaryField) (hn : 1 < F.degree)
    (c : ActionEquiv (s.action.comp (L.subgroupOf J).subtype) (binarySymplectic F))
    (e : L ≃* Sp F.Carrier) (t : D) :
    PreservesDiagram (MulAut.congr e (MulAut.conjNormal t)) := by
  let i : L.subgroupOf J ≃* L := subgroupOfEquivOfLe hLJ
  let β : MulAut (L.subgroupOf J) := i.trans ((MulAut.conjNormal t).trans i.symm)
  let b := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t)
  have hb (l : L.subgroupOf J) (w : W) :
      b ((ρ.comp J.subtype) l w) = (ρ.comp J.subtype) (β l) (b w) := by
    change ρ t (ρ l.val.val w) = ρ (t*l.val.val*t⁻¹) (ρ t w)
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  let E := s.twistedActionEquiv β b hb
  let B := c.linearEquiv.symm.trans (E.linearEquiv.trans c.linearEquiv)
  let a₀ : MulAut (Sp F.Carrier) := c.groupEquiv.symm.trans (β.trans c.groupEquiv)
  have hF : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact (show 2^1 < 2^F.degree from Nat.pow_lt_pow_right (by decide) hn)
  have hd : PreservesDiagram a₀ := diagram_of_intertwiner hF a₀ B
    (c.conjugate_intertwiner β E.linearEquiv (s.twistedActionEquiv_intertwines β b hb))
  let f : MulAut (Sp F.Carrier) := e.symm.trans (i.symm.trans c.groupEquiv)
  have he : MulAut.congr e (MulAut.conjNormal t) = f⁻¹ * a₀ * f := by
    ext x
    simp [f,a₀,β,i,MulAut.congr_apply]
  rw [he]
  apply (mem_parabolicClassAction_ker_iff hF _).mp
  exact (inferInstance : (parabolicClassAction hF).ker.Normal).conj_mem a₀
    ((mem_parabolicClassAction_ker_iff hF _).mpr hd) f⁻¹
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The actual natural symplectic moved section fixes the diagram, so both
literal parabolic residuals belong to the original full local family. -/
theorem localFamily_symplectic_source_residual_members
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (a : d.NormalizerAction K) :
    letI := a.reduced.elementary
    ∀ (J : Subgroup ((K ⊔ d.normalizerSylow K : Subgroup G) ⧸
        centralizer (d.normalizerModule K : Set (K ⊔ d.normalizerSylow K : Subgroup G))))
      (_hLJ : d.normalizerImage K ≤ J)
      (s : MovedSection (a.representation.comp J.subtype) ((d.normalizerImage K).subgroupOf J))
      (F : BinaryField), 1 < F.degree →
      ActionEquiv (s.action.comp ((d.normalizerImage K).subgroupOf J).subtype)
        (binarySymplectic F) →
    ∃ e' : d.normalizerImage K ≃* Sp F.Carrier,
      ∀ P ∈ ({pointParabolic,planeParabolic} : Set (Subgroup (Sp F.Carrier))),
        d.normalizerParabolicResidual K (P.map e'.symm.toMonoidHom) ∈ Chapter1.LIn d.G1 d.S := by
  let := a.reduced.elementary
  intro J hLJ s F hn c
  let e : d.normalizerImage K ≃* Sp F.Carrier :=
    (subgroupOfEquivOfLe hLJ).symm.trans c.groupEquiv
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.2
  have hfour : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  let ec := (MulEquiv.ofBijective a.coreToImage
    (a.symplectic_four_core_bijective hq hfour e)).trans e
  have hnK := d.localFamily_symplectic_four_normalizes hG h hK hq ec
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  let q₀ := e.toMonoidHom.comp (d.toNormalizerImage K)
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (d.toNormalizerImage_surjective K)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F.Carrier) (Q.mapSurjective hq₀)
    (unipotentSylow F.card_eq hn.le)
  let e' := e.trans (MulAut.conj g)
  let q := e'.toMonoidHom.comp (d.toNormalizerImage K)
  have hU : (Q : Subgroup K).map q = unipotent := by
    have hh := congrArg (fun U : Sylow 2 (Sp F.Carrier) => (U : Subgroup (Sp F.Carrier))) hg
    change ((Q : Subgroup K).map q₀).map (MulAut.conj g).toMonoidHom = unipotent at hh
    rw [map_map] at hh
    exact hh
  have hQL : (Q : Subgroup K) = (d.S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.S ⊓ K ≤ K from inf_le_right)]
    exact hQ
  let H := K ⊔ d.normalizerSylow K
  let qH := QuotientGroup.mk' (centralizer (d.normalizerModule K : Set H))
  let : (d.normalizerImage K).Normal := by
    change ((K.subgroupOf H).map qH).Normal
    rw [a.fitting]
    infer_instance
  have hSH : d.S ≤ H := by
    have he : d.normalizerSylow K = d.S := inf_eq_left.mpr hnK
    change d.S ≤ K ⊔ d.normalizerSylow K
    rw [he]
    exact le_sup_right
  let j : d.S →* H := inclusion hSH
  let α : d.S →* MulAut (Sp F.Carrier) := (MulAut.congr e').toMonoidHom.comp
    (MulAut.conjNormal.comp (qH.comp j))
  have heq (x : d.S) (k : K) :
      q (K.normalizerMonoidHom (inclusion hnK x) k) = α x (q k) := by
    change e' (d.toNormalizerImage K _) =
      e' ((MulAut.conjNormal (qH (j x))) (e'.symm (e' (d.toNormalizerImage K k))))
    rw [e'.symm_apply_apply]
    congr 1
  have hnSK : d.S ≤ normalizer ((d.S ⊓ K) : Set G) :=
    (le_inf d.S.le_normalizer hnK).trans inf_normalizer_le_normalizer_inf
  have hUi (x : d.S) : unipotent.map (α x).toMonoidHom = unipotent := by
    have hh := EquivariantLift.map_invariant K q hnK α heq (D := d.S ⊓ K) hnSK x
    rw [←hQL,hU] at hh
    exact hh
  have hpair (x : d.S) :
      pointParabolic.map (α x).toMonoidHom = pointParabolic ∧
      planeParabolic.map (α x).toMonoidHom = planeParabolic :=
    parabolic_pair_map_of_unipotent_map F.card_eq hn _
      (moved_symplectic_diagram a.representation (d.normalizerImage K) J hLJ s F hn c
        e' (qH (j x))) (hUi x)
  refine ⟨e',?_⟩
  intro P hP
  have hPi (s : d.S) : P.map (α s).toMonoidHom = P := by
    rcases hP with rfl | hP
    · exact (hpair s).1
    · have he : P = planeParabolic := hP
      subst P
      exact (hpair s).2
  let B := (P.comap q).map K.subtype
  let R := d.normalizerParabolicResidual K (P.map e'.symm.toMonoidHom)
  have hR : R = (solvableResidual B).map B.subtype := by
    dsimp only [R]
    rw [d.normalizerParabolicResidual_eq_in_K]
    have he : (P.map e'.symm.toMonoidHom).comap (d.toNormalizerImage K) = P.comap q := by
      ext k
      change d.toNormalizerImage K k ∈ P.map e'.symm.toMonoidHom ↔ e' (d.toNormalizerImage K k) ∈ P
      constructor
      · rintro ⟨y,hy,he⟩
        rw [←he]
        change e' (e'.symm y) ∈ P
        rw [e'.apply_symm_apply]
        exact hy
      · intro hx
        exact ⟨_,hx,e'.symm_apply_apply _⟩
    rw [he,map_embedded_solvableResidual_of_hom]
  have hnB : d.S ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx b hb
    obtain ⟨k,hk,rfl⟩ := hb
    let x₀ : d.S := ⟨x,hx⟩
    refine ⟨K.normalizerMonoidHom (inclusion hnK x₀) k,?_,rfl⟩
    change q (K.normalizerMonoidHom (inclusion hnK x₀) k) ∈ P
    rw [heq]
    exact hPi x₀ ▸ mem_map_of_mem (α x₀).toMonoidHom hk
  have hnR : d.S ≤ normalizer (R : Set G) := by
    rw [hR]
    exact hnB.trans (normalizer_le_normalizer_characteristic_image B (solvableResidual B))
  let : Group.IsPerfect R := hR ▸ Group.IsPerfect.map B.subtype
  obtain ⟨hfit,⟨er⟩⟩ := a.symplectic_four_residual_data hq F.card_eq hn e' P hP
  let : IsSimpleGroup SL(2,F.Carrier) := NaturalExtension.model_simple (by omega)
  let : IsSimpleGroup (R ⧸ pCore 2 R) := er.isSimpleGroup
  let : Nontrivial R := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (pCore 2 R))
  have hz : center (R ⧸ pCore 2 R) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (R ⧸ pCore 2 R)) inferInstance with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
  let : IsQuasisimple (R ⧸ pCore 2 R) :=
    { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hc : R.pCoreIn 2 ≠ ⊥ := by
    intro hh
    have hb : pCore 2 R = ⊥ := (map_eq_bot_iff_of_injective _ R.subtype_injective).mp hh
    have ht := centralizer_generalizedFitting_le R
    rw [hfit,hb] at ht
    rw [show centralizer ((⊥ : Subgroup R) : Set R) = ⊤ from
      centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup R) ≤ center R from bot_le)] at ht
    have ht' : (⊤ : Subgroup R) = ⊥ := bot_unique ht
    exact (top_ne_bot : (⊤ : Subgroup R) ≠ ⊥) ht'
  exact ⟨(d.normalizerParabolicResidual_le K _).trans hK.1,
    (Chapter1.mem_LIn_of_normalized_perfect hK.2.2.1
      ((d.normalizerParabolicResidual_le K _).trans le_sup_left) hnR hc).2⟩
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The natural symplectic row is impossible for every escaping member of
L(G₁,S). Its two actual residuals are nonblocks and generate that same member. -/
theorem localFamily_symplectic_source_impossible
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (a : d.NormalizerAction K) :
    letI := a.reduced.elementary
    ∀ (J : Subgroup ((K ⊔ d.normalizerSylow K : Subgroup G) ⧸
        centralizer (d.normalizerModule K : Set (K ⊔ d.normalizerSylow K : Subgroup G))))
      (_hLJ : d.normalizerImage K ≤ J)
      (s : MovedSection (a.representation.comp J.subtype) ((d.normalizerImage K).subgroupOf J))
      (F : BinaryField), 1 < F.degree →
      ActionEquiv (s.action.comp ((d.normalizerImage K).subgroupOf J).subtype)
        (binarySymplectic F) → False := by
  let := a.reduced.elementary
  intro J hLJ s F hn c
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.2
  have hfour : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  obtain ⟨e',hfam⟩ := d.localFamily_symplectic_source_residual_members hG h hK hq a J hLJ s F hn c
  have hdata := a.symplectic_four_residual_data hq F.card_eq hn e'
  have hns := a.symplectic_four_residuals_not_short e' F.card_eq hn
  have hplace (P : Subgroup (Sp F.Carrier)) (hP : P ∈ ({pointParabolic,planeParabolic} : Set (Subgroup (Sp F.Carrier)))) :
      d.normalizerParabolicResidual K (P.map e'.symm.toMonoidHom) ≤ d.MZ := by
    let R := d.normalizerParabolicResidual K (P.map e'.symm.toMonoidHom)
    have hr := hfam P hP
    let : Group.IsPerfect R := Chapter1.mem_L_isPerfect hr.2
    obtain ⟨hf,⟨er⟩⟩ := hdata P hP
    let : IsSimpleGroup SL(2,F.Carrier) := NaturalExtension.model_simple (by omega)
    let : IsSimpleGroup (R ⧸ pCore 2 R) := er.isSimpleGroup
    have hz : center (R ⧸ pCore 2 R) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (R ⧸ pCore 2 R)) inferInstance with hz | hz
      · exact hz
      · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
    let hqr : IsQuasisimple (R ⧸ pCore 2 R) :=
      { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
    have hnot : ¬ ChapterC.IsShort R := by
      rcases hP with rfl | hP
      · exact hns.1
      · have he : P = planeParabolic := hP
        subst P
        exact hns.2
    exact d.localFamily_nonblock_le_MZ hG hempty hM hJ hu h hr hqr hf
      (fun hc => hnot hc.short) F.Carrier er
  apply hout
  rw [←a.symplectic_four_residuals_generate hq e' F.card_eq hn]
  exact sup_le (hplace _ (Or.inl rfl)) (hplace _ (Or.inr rfl))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
