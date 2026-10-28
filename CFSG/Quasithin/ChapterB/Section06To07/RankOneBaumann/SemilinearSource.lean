module

public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.SemilinearImages
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.FrattiniSource
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.SL2Geometry
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Nonsolvable
public import CFSG.Quasithin.ChapterB.Section02.Baumann.ActionQuotient
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.GroupTheory.PResidual.NormalSubgroup
/-!
# The normal semilinear rank-one Baumann source theorem

The preimage of a marked normal SL₂ layer cannot lie in the solvable
minimal-parabolic core. The normal-subgroup residual dichotomy and perfectness
therefore identify its literal image with the two-residual image. Two original
residual conjugates of the Thompson subgroup generate this layer. The sharp
natural offender inequality gives its fixed codimension; the actual residual
fixed-kernel marker gives twice that codimension for the residual.

Together with the universal minimal-parabolic Frattini theorem these facts
establish B.2.18's alpha decomposition. The Baumann image is a layer Sylow, and
the exact centralizer quotient and original centralizer Sylow lift it back to
the original group. The ambient image may include field automorphisms; the
module's fixed kernel is retained and no direct-sum splitting is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.6.10,
printed p.117, with B.2.18 and B.2.20, printed pp.81–82.
-/

public section
open Subgroup Stellmacher Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
open BaumannArgument
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
private theorem perfect_twoPerfect {D : Type*} [Group D] [Finite D]
    [Group.IsPerfect D] : IsPPerfect 2 D := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (D ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (D ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (D ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (D ⧸ N) inferInstance
/-- The original two-residual has exactly the marked normal SL₂ layer as its image. -/
theorem residual_image_eq_normal_natural_layer (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (q : G →* H) (hq : Function.Surjective q)
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hF : 2 < Nat.card F) :
    (pResidual 2 G).map q = L := by
  have hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F))
  have hlarge : 3 < Nat.card F := by
    have hn : 2 ≤ Module.finrank (ZMod 2) F := by
      by_contra! hh
      have hn1 : Module.finrank (ZMod 2) F ≤ 1 := by omega
      have hl := Nat.pow_le_pow_right (by decide : 0 < 2) hn1
      rw [← hcard] at hl
      norm_num at hl
      omega
    have hl := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    rw [← hcard] at hl
    norm_num at hl
    omega
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three F hlarge
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (Matrix.SpecialLinearGroup.upperUnipotentHom_injective F).nontrivial
  let : Nontrivial L := e.surjective.nontrivial
  have hK : ¬ L.comap q ≤ minimalParabolicCore T hP := by
    intro hc
    let : Group.IsSolvable (minimalParabolicCore T hP) := minimalParabolic_core_solvable T hP
    let : Group.IsSolvable (L.comap q) :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hc)
    let j : L.comap q →* L := (q.comp (L.comap q).subtype).codRestrict L (fun g => g.property)
    have hj : Function.Surjective j := by
      intro l
      obtain ⟨g, hg⟩ := hq l
      exact ⟨⟨g, by change q g ∈ L; rw [hg]; exact l.property⟩, Subtype.ext hg⟩
    exact Group.IsPerfect.not_isSolvable L (Group.isSolvable_of_surjective hj)
  have hr : pResidual 2 G ≤ L.comap q :=
    (minimalParabolic_normal_subgroup_residual_dichotomy T hP (L.comap q)).resolve_left hK
  apply le_antisymm (map_le_iff_le_comap.mpr hr)
  rw [map_pResidual_of_surjective 2 q hq]
  exact le_pResidual_of_isPPerfect L perfect_twoPerfect

/-- An original residual conjugator makes the two literal Thompson images generate the normal layer. -/
theorem exists_residual_conjugate_thompson_images_sup_eq_layer (T : Sylow 2 G) (q : G →* H) (hq : Function.Surjective q)
    (L : Subgroup H) [L.Normal] (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hres : (pResidual 2 G).map q = L)
    (J : Subgroup G) (hJ : J.map q = (T : Subgroup G).map q ⊓ L) :
    ∃ g ∈ pResidual 2 G, J.map q ⊔ (J.map (MulAut.conj g).toMonoidHom).map q = L := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let P := T.mapSurjective hq
  obtain ⟨Q,hQ⟩ := P.exists_sylow_map_eq_inf_of_normal L
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hn : normalizer (R : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ≠ ⊤ := by
    intro hh
    exact Matrix.SpecialLinearGroup.no_normal_sylow F 2 R (normalizer_eq_top_iff.mp hh)
  obtain ⟨z,_,hz⟩ := SetLike.not_le_iff_exists.mp (show ¬ (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ normalizer (R : Set _) from fun hh => hn (top_unique hh))
  have hgen := Matrix.SpecialLinearGroup.sylow_sup_conjugate_eq_top_of_not_mem_normalizer R hz
  have hJQ : J.map q = (Q : Subgroup L).map L.subtype := hJ.trans hQ.symm
  have hzL : ((e.symm z : L) : H) ∈ (pResidual 2 G).map q := by
    rw [hres]
    exact (e.symm z).property
  obtain ⟨g,hg,hgq⟩ := mem_map.mp hzL
  refine ⟨g,hg,?_⟩
  let k : Matrix.SpecialLinearGroup (Fin 2) F →* H := L.subtype.comp e.symm.toMonoidHom
  have hRk : (R : Subgroup _).map k = J.map q := by
    change ((Q : Subgroup L).map e.toMonoidHom).map k = _
    rw [map_map,hJQ]
    congr 1
    apply MonoidHom.ext
    intro a
    exact congrArg Subtype.val (e.symm_apply_apply a)
  have hkz : k z = q g := hgq.symm
  have hconj : ((R : Subgroup _).map (MulAut.conj z).toMonoidHom).map k =
      (J.map (MulAut.conj g).toMonoidHom).map q := by
    rw [map_map,show k.comp (MulAut.conj z).toMonoidHom =
      (MulAut.conj (q g)).toMonoidHom.comp k from by
        apply MonoidHom.ext
        intro a
        change k (z*a*z⁻¹) = q g * k a * (q g)⁻¹
        simp only [map_mul,map_inv,hkz],←map_map,hRk,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    change q g * q a * (q g)⁻¹ = q (g*a*g⁻¹)
    simp only [map_mul,map_inv]
  have hh := congrArg (map k) hgen
  rw [Subgroup.map_sup,hRk,hconj] at hh
  exact hh.trans (by
    change (⊤ : Subgroup _).map (L.subtype.comp e.symm.toMonoidHom) = L
    rw [←map_map, map_top_of_surjective _ e.symm.surjective, ←MonoidHom.range_eq_map,
      Subgroup.range_subtype])

end CFSG.Quasithin.ChapterB.RankOneBaumann
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
open Subgroup Stellmacher Representation BaumannArgument Theory.GroupTheory
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
variable (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (hF : 2 < Nat.card F)
    (f : Additive U →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = ρ g (f v))
include e hnat hF hfaith hf he
omit T hUT hJ in
/-- The natural equivariant quotient excludes strong offenders in the original action. -/
theorem noStrong_of_semilinear_quotient (R : Subgroup G) : NoStrongOffenders U R := by
  apply noStrong_of_centralizer_quotient U q hq hker
  rintro ⟨A,hA⟩
  apply SL2NaturalOffenders.Ratios.not_strong L e ρ hnat hF hfaith
  exact ⟨A,hA.1,(BinaryOffender.fixedCodim_le_of_equivariant_surjection
    _ ρ f hf he A).trans_lt hA.2⟩

include hUT hJ in
/-- The moving Thompson action has fixed codimension equal to the defining field degree. -/
theorem thompson_fixedCodim_of_semilinear_quotient :
    fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) = Module.finrank (ZMod 2) F := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let P := T.mapSurjective hq
  let S : Subgroup H := (P : Subgroup H) ⊓ L
  have hj := (thompson_baumann_images_of_semilinear_quotient
    T U q hq hker hUT hJ L e ρ hfaith hnat hF f hf he).1
  have hex : ∃ B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G), B.map q ≠ ⊥ := by
    by_contra! hn
    apply hJ
    rw [←hker]
    exact sSup_le fun B hB => (map_eq_bot_iff B).mp (hn B hB)
  obtain ⟨B,hB,hne⟩ := hex
  have hb : BinaryOffender.IsOffender α (B.map q) :=
    (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      U q hq hker (T : Subgroup G) B hUT hB hne).isOffender
  have hBS : B.map q = S :=
    (SL2NaturalOffenders.Ratios.offender_iff_eq_sylowInf L e ρ hnat hF hfaith P
      (map_mono hB.1)).mp ⟨hb.1,
        (BinaryOffender.fixedCodim_le_of_equivariant_surjection α ρ f hf he _).trans hb.2⟩
  have hS : BinaryOffender.IsOffender α S := hBS ▸ hb
  obtain ⟨Q,hQ⟩ := P.exists_sylow_map_eq_inf_of_normal L
  have hcod : BinaryOffender.fixedCodim ρ S = Module.finrank (ZMod 2) F := by
    rw [show S = (Q : Subgroup L).map L.subtype from hQ.symm]
    exact SL2NaturalOffenders.Ratios.sylowImage_fixedCodim L e ρ hnat Q
  have hrank : BinaryOffender.rank S = Module.finrank (ZMod 2) F := by
    rw [show S = (Q : Subgroup L).map L.subtype from hQ.symm]
    exact SL2NaturalOffenders.Ratios.sylowImage_rank L e Q
  rw [fixedCodim_eq_centralizer_quotient U q hq hker,hj]
  change BinaryOffender.fixedCodim α S = _
  apply le_antisymm (hS.2.trans_eq hrank)
  rw [←hcod]
  exact BinaryOffender.fixedCodim_le_of_equivariant_surjection α ρ f hf he S

omit T hUT hJ L e ρ hfaith hnat hF he [Finite H] in
/-- The literal residual fixed-kernel marker gives twice the defining field degree. -/
theorem residual_fixedCodim_of_marked_kernel
    (hk : f.ker = BinaryOffender.fixedSpace
      (NormalElementaryQuotient.representation U q hq hker) ((pResidual 2 G).map q)) :
    fixedCodim U (pResidual 2 G) = 2 * Module.finrank (ZMod 2) F := by
  rw [fixedCodim_eq_centralizer_quotient U q hq hker,BinaryOffender.fixedCodim,←hk]
  exact (f.quotKerEquivOfSurjective hf).finrank_eq.trans
    (by simp [Module.finrank_pi_fintype,two_mul])
end CFSG.Quasithin.ChapterB.RankOneBaumann
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
open Subgroup Stellmacher Representation BaumannArgument Theory.GroupTheory
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
/-- The normal semilinear natural source marker proves the original Baumann Sylow theorem and alpha decomposition. -/
theorem semilinear_baumann_sylow_and_alpha
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (hF : 2 < Nat.card F)
    (f : Additive U →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = ρ g (f v))
    (hk : f.ker = BinaryOffender.fixedSpace
      (NormalElementaryQuotient.representation U q hq hker) ((pResidual 2 G).map q)) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
      thompsonAlpha (T : Subgroup G) =
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) := by
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hres := residual_image_eq_normal_natural_layer T hP q hq L e hF
  obtain ⟨hJq,hBq⟩ := thompson_baumann_images_of_semilinear_quotient
    T U q hq hker hUT hJ L e ρ hfaith hnat hF f hf he
  obtain ⟨g,hg,hgen⟩ := exists_residual_conjugate_thompson_images_sup_eq_layer
    T q hq L e hres (elementaryAbelianMaxJ (T : Subgroup G)) hJq
  have hgenJ : (pResidual 2 G).map q ≤
      (elementaryAbelianMaxJ (T : Subgroup G)).map q ⊔
      ((elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom).map q := by
    rw [hres,hgen]
  have hcod : 2 * fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) ≤
      fixedCodim U (pResidual 2 G) := by
    rw [thompson_fixedCodim_of_semilinear_quotient T U q hq hker hUT hJ L e ρ hfaith hnat hF f hf he,
      residual_fixedCodim_of_marked_kernel U q hq hker f hf hk]
  have halpha := (two_conjugate_alpha_and_saturation T hP U hU hJ q hker
    (residual_centralizer_le_coreFrattini T hP U hU hJ)
    (noStrong_of_semilinear_quotient U q hq hker L e ρ hfaith hnat hF f hf he _) g hg hgenJ hcod).2.1
  refine ⟨?_,halpha⟩
  apply sylow_lift_of_decomposition U (T : Subgroup G) (pResidual 2 G)
    T.isPGroup' halpha (centralizer_sylow T U)
  let k : (G ⧸ centralizer (U : Set G)) →* H := QuotientGroup.lift _ q hker.symm.le
  have hki : Function.Injective k := (QuotientGroup.injective_lift_iff (centralizer (U : Set G)) q hker.symm.le).mpr hker.symm
  have hmap (A : Subgroup G) : (A.map (actionMap U)).map k = A.map q := by
    rw [map_map]
    rfl
  apply (Chapter1.IsSylowIn.map_iff k hki).mp
  rw [Subgroup.map_sup,hmap,hmap,hBq,hres,sup_eq_left.mpr inf_le_right]
  obtain ⟨Q,hQ⟩ := (T.mapSurjective hq).exists_sylow_map_eq_inf_of_normal L
  exact ⟨Q,hQ⟩
end CFSG.Quasithin.ChapterB.RankOneBaumann
