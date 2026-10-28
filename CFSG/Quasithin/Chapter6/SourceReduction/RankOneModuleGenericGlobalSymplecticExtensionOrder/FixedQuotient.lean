module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedPair
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.FixedQuotient

/-!
# The field-four obstruction and the original ambient Sylow

Over the four-element field the outer automorphism group of Sp4 is a
two-group. The chosen full-normalizer marking therefore puts each fixed
endpoint two-residual in the inner parabolic. Its two-core has trivial
determinant and belongs to the original local factor. Conjugation transports
both placements through the same prescribed full normalizer and marking.

Apply this to the two fixed residual four-groups and their already constructed
D8 join. The original root witness and its conjugator are retained. The join
avoids the conjugate normalizer's two-core, hence also the conjugate local's
two-core, so the literal local quotient map is injective on this same D8.
The quotient is the original PSL2(4), of order sixty: eight cannot divide sixty.
This excludes all outer involutions selected by the earlier transfer argument
and proves S=T, including n=2 and both amalgam orientations.

Consequently the full nonroot involution centralizer lies in the whole common
normalizer. The three marked class/centralizer comparisons and the ambient
order bound for the same extension remain subsequent obligations.

Source: Aschbacher--Smith F.4.37 and F.4.39, printed pp.293--294, applied in
5.3.3, p.659 of refs/quasithin.pdf. The whole residual of H is retained.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he


/-- Field and scalar elimination in either full normalizer, using the chosen
full-normalizer marking and its exact inner intersection. -/
theorem Preparation.symplectic_residual_core_le_local_four
    (hq : Nat.card F=4) (i : Fin 2) (C : Subgroup G)
    (hCM : C≤normalizer (![L,residual H] i : Set G)) :
    ((pResidual 2 C).map C.subtype).pCoreIn 2 ≤ ![L,residual H] i := by
  let a := d.symplecticNormalizerMarking h hH hp F hm hF he
  have hmn := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1
  have hm' : 1<m := hmn.symm ▸ h.exponent
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  have hres (i : Fin 2) : (![L,residual H] i).subgroupOf (P i) = solvableResidual (P i) := by
    rw [←d.parabolic_residuals h hH.1.1.2 hp i]
    exact comap_map_eq_self_of_injective (P i).subtype_injective _
  have hpoint (j : Fin 2) (e : P j ≃* pointParabolic (F := F)) :
      ((![L,residual H] j).subgroupOf (P j)).map
        (pointParabolic.subtype.comp e.toMonoidHom) = pointLocal := by
    rw [hres,←map_map,map_solvableResidual_eq e.toMonoidHom e.surjective]
    exact pointParabolic_solvableResidual_eq hF hm'
  have hplane (j : Fin 2) (e : P j ≃* planeParabolic (F := F)) :
      ((![L,residual H] j).subgroupOf (P j)).map
        (planeParabolic.subtype.comp e.toMonoidHom) = planeLocal := by
    rw [hres,←map_map,map_solvableResidual_eq e.toMonoidHom e.surjective]
    exact planeParabolic_solvableResidual_eq hF hm'
  rcases a.comparison with ⟨e,f,hl,hr,_⟩ | ⟨e,f,hl,hr,_⟩
  · fin_cases i
    · apply SourceFusionOrder.residual_core_le_marked_local hq
        (normalizer (L : Set G)) (P 0) L C hCM
        (point F) e.left (a.extension.left.subtype.comp f.left.toMonoidHom)
      · exact SourceFusionOrder.marked_inner_preimage _ _ _ _ a.left_le
          e.left f.left a.extension.left_inner hl
      · exact hpoint 0 e.left
    · apply SourceFusionOrder.residual_core_le_marked_local hq
        (normalizer (residual H : Set G)) (P 1) (residual H) C hCM
        (plane F) e.right (a.extension.right.subtype.comp f.right.toMonoidHom)
      · exact SourceFusionOrder.marked_inner_preimage _ _ _ _ a.right_le
          e.right f.right a.extension.right_inner hr
      · exact hplane 1 e.right
  · fin_cases i
    · apply SourceFusionOrder.residual_core_le_marked_local hq
        (normalizer (L : Set G)) (P 0) L C hCM
        (plane F) e.left (a.extension.right.subtype.comp f.left.toMonoidHom)
      · exact SourceFusionOrder.marked_inner_preimage _ _ _ _ a.left_le
          e.left f.left a.extension.right_inner hl
      · exact hplane 0 e.left
    · apply SourceFusionOrder.residual_core_le_marked_local hq
        (normalizer (residual H : Set G)) (P 1) (residual H) C hCM
        (point F) e.right (a.extension.left.subtype.comp f.right.toMonoidHom)
      · exact SourceFusionOrder.marked_inner_preimage _ _ _ _ a.right_le
          e.right f.right a.extension.left_inner hr
      · exact hpoint 1 e.right

/-- The core placement respects any prescribed ambient conjugator. -/
theorem Preparation.symplectic_residual_core_le_conjugate_local_four
    (hq : Nat.card F=4) (i : Fin 2) (g : G) (D : Subgroup G)
    (hDM : D≤(normalizer (![L,residual H] i : Set G)).map (MulAut.conj g).toMonoidHom) :
    ((pResidual 2 D).map D.subtype).pCoreIn 2 ≤
      (![L,residual H] i).map (MulAut.conj g).toMonoidHom := by
  let c := MulAut.conj g
  let C := D.map c.symm.toMonoidHom
  have hCM : C≤normalizer (![L,residual H] i : Set G) := by
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨z,hz,hzy⟩ := hDM hy
    have heq : c.symm y=z := by rw [←hzy]; exact c.symm_apply_apply z
    exact heq.symm ▸ hz
  have hh := map_mono (f := c.toMonoidHom)
    (d.symplectic_residual_core_le_local_four h hH hp F hm hF he hq i C hCM)
  have hCD : C.map c.toMonoidHom=D := by
    rw [map_map]
    have hc : c.toMonoidHom.comp c.symm.toMonoidHom=MonoidHom.id G := by
      ext x
      exact c.apply_symm_apply x
    rw [hc,map_id]
  rwa [map_pCoreIn_of_injective 2 _ _ c.injective,map_embedded_pResidual,hCD] at hh

/-- Both fixed residual cores lie in the same conjugate original local. -/
theorem Preparation.symplectic_outer_fixed_cores_le_conjugate_local
    (f : T) (_hf : orderOf f=2) (ho : f.val ∉ sourceS L H)
    (i : Fin 2) (g : G)
    (hC : centralizer ({f.val} : Set G) ≤
      (normalizer (![L,residual H] i : Set G)).map (MulAut.conj g).toMonoidHom) :
    ∀ j : Fin 2,
      ((pResidual 2 (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) j ⊓
        centralizer ({f.val} : Set G) : Subgroup G)).map
        (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) j ⊓
          centralizer ({f.val} : Set G)).subtype).pCoreIn 2 ≤
      (![L,residual H] i).map (MulAut.conj g).toMonoidHom := by
  have hst : sourceS L H≠(T : Subgroup G) := fun hh => ho (hh.symm ▸ f.property)
  have hq := (d.symplectic_proper_inner_sylow_field_four h hH hp F hm hF he hst).2.2.1
  intro j
  exact d.symplectic_residual_core_le_conjugate_local_four h hH hp F hm hF he
    hq i g _ (inf_le_right.trans hC)

/-- The actual D8 cannot embed in the conjugate local PSL2(4) section. -/
theorem Preparation.symplectic_outer_involution_false
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ sourceS L H) : False := by
  have hst : sourceS L H≠(T : Subgroup G) := fun hh => ho (hh.symm ▸ f.property)
  have hn := d.symplectic_proper_inner_sylow_exponent h hH hp F hm hF he hst
  obtain ⟨i,z,_hz,_hzR,g,_hg,hC,hJM,⟨e⟩,hdis,_hinj⟩ :=
    d.symplectic_outer_fixed_dihedral_normalizer_quotient h hH hp F hm hF he f hf ho
  let c := MulAut.conj g
  let K₀ := ![L,residual H] i
  let K := K₀.map c.toMonoidHom
  let M := (normalizer (K₀ : Set G)).map c.toMonoidHom
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let D : Fin 2 → Subgroup G := fun j => P j ⊓ centralizer ({f.val} : Set G)
  let U : Fin 2 → Subgroup G := fun j => ((pResidual 2 (D j)).map (D j).subtype).pCoreIn 2
  let J := U 0⊔U 1
  have hUK := d.symplectic_outer_fixed_cores_le_conjugate_local h hH hp F hm hF he
    f hf ho i g hC
  have hJK : J≤K := sup_le (hUK 0) (hUK 1)
  have hKM : K≤M := map_mono K₀.le_normalizer
  have hMK : M≤normalizer (K : Set G) := le_normalizer_map c.toMonoidHom
  have hQ : K.pCoreIn 2≤M.pCoreIn 2 := pCoreIn_mono_of_normalizes hKM hMK
  let q : J→*K⧸pCore 2 K := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hJK)
  have hq : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxQ : x.val∈K.pCoreIn 2 := by
      refine ⟨inclusion hJK x,?_,rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    exact mem_bot.mpr (Subtype.ext (disjoint_def.mp hdis x.property (hQ hxQ)))
  have hb : ChapterC.IsL2EvenBlock K₀ 2 := by
    obtain ⟨_,hL,hR⟩ := d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he
    rw [hn] at hL hR
    fin_cases i
    · exact hL
    · exact hR
  obtain ⟨_,_,E,_,_,_,hpsl,_⟩ := hb
  obtain ⟨E',_,_,hE',⟨a⟩⟩ := hpsl
  have hc₀ : Nat.card (K₀⧸pCore 2 K₀)=60 := by
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := E') 2
    rw [hE'] at hc
    norm_num [Fin.prod_univ_two] at hc
    rw [Nat.card_congr a.toEquiv]
    omega
  let ek : K₀≃*K := c.subgroupMap K₀
  let eqk := QuotientGroup.congr _ _ ek (pCore_map_iso 2 ek)
  have hc : Nat.card (K⧸pCore 2 K)=60 :=
    (Nat.card_congr eqk.symm.toEquiv).trans hc₀
  have hd := card_dvd_of_injective q hq
  rw [hc,Nat.card_congr e.toEquiv,DihedralGroup.nat_card] at hd
  norm_num at hd

/-- The original inner Sylow is the ambient Sylow, including field order four. -/
theorem Preparation.symplectic_sourceS_eq_sylow : sourceS L H=(T : Subgroup G) := by
  by_contra hst
  obtain ⟨f,hf,ho,_⟩ := d.symplectic_outer_fixed_derived_disjoint_roots h hH hp F hm hF he hst
  exact d.symplectic_outer_involution_false h hH hp F hm hF he f hf ho

/-- The third involution centralizer is contained in the full common normalizer,
with the Sylow equality now proved for every original exponent n>1. -/
theorem Preparation.symplectic_square_centralizer_le_middle
    (z : sourceS L H) (hz : orderOf z=2) (hsq : ∃ y : sourceS L H, y^2=z) :
    centralizer ({z.val} : Set G)≤normalizer (L : Set G)⊓normalizer (residual H : Set G) :=
  d.symplectic_square_centralizer_le_middle_of_sylow h hH hp F hm hF he
    (d.symplectic_sourceS_eq_sylow h hH hp F hm hF he) z hz hsq

/-- The whole inner Sylow center has the actual common normalizer as its
normalizer, with no additional Sylow-placement assumption. -/
theorem Preparation.symplectic_center_normalizer_eq_middle :
    normalizer ((center (sourceS L H)).map (sourceS L H).subtype : Set G)=
      normalizer (L : Set G)⊓normalizer (residual H : Set G) :=
  d.symplectic_center_normalizer_eq_middle_of_sylow h hH hp F hm hF he
    (d.symplectic_sourceS_eq_sylow h hH hp F hm hF he)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
