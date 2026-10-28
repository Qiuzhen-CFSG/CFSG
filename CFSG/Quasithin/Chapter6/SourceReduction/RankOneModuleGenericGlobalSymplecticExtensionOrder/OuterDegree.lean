module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.MarkedCentralizers
public import CFSG.Quasithin.Chapter5.Section03SymplecticSource.OuterDegree

/-!
# Odd outer degree for the same prepared symplectic extension

The coherent pure-middle marking identifies the full outer degree with the
original Borel index in the whole normalizer intersection. Since S=T, this
index is odd. Consequently the native unipotent subgroup remains Sylow in
the full carrier, and every carrier involution has a literal native lift.
The carrier order formula retains the full extension factor; it makes no
comparison with the order of the original ambient group.

Source: Aschbacher--Smith F.4.38 and the setup of F.4.43, printed
pp.294,296, applied through 5.3.2--3, pp.658--659 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] {F : Type} [Field F] [CharP F 2]

private theorem middle_inner_preimage {C D : Subgroup G} (hCD : C≤D)
    (E : SourceExtension F) (e : C≃*borel (F := F)) (f : D≃*E.middle)
    (hmark : ∀ c, (f (inclusion hCD c)).val=MulAut.conj (e c).val) :
    ((inner F).subgroupOf E.middle).comap f.toMonoidHom=C.subgroupOf D := by
  ext x
  change (f x).val∈inner F ↔ x.val∈C
  constructor
  · intro hx
    have hm : (f x).val∈E.middle⊓inner F := ⟨(f x).property,hx⟩
    rw [E.middle_inner] at hm
    obtain ⟨b,hb,he⟩ := hm
    let c : C := e.symm ⟨b,hb⟩
    have hc : inclusion hCD c=x := by
      apply f.injective
      apply Subtype.ext
      exact (hmark c).trans ((congrArg (fun v : borel (F := F) => MulAut.conj v.val)
        (e.apply_symm_apply ⟨b,hb⟩)).trans he)
    exact congrArg (fun v : D => v.val) hc ▸ c.property
  · intro hx
    let c : C := ⟨x.val,hx⟩
    exact ⟨(e c).val,hmark c |>.symm⟩

/-- The full extension degree equals the original pure-middle index. -/
theorem SymplecticNormalizerMarking.outer_index_eq_source {L K S : Subgroup G}
    (a : SymplecticNormalizerMarking L K S F) :
    a.extension.innerMap.range.index =
      (ChapterF.Source.parabolic ![L,K] S 0⊓ChapterF.Source.parabolic ![L,K] S 1).relIndex
        (normalizer (L : Set G)⊓normalizer (K : Set G)) := by
  rw [Chapter5.Section03SymplecticSource.extension_outer_index_eq]
  have hCD := le_inf (inf_le_left.trans a.left_le) (inf_le_right.trans a.right_le)
  rcases a.comparison with ⟨e,f,_,_,hd⟩ | ⟨e,f,_,_,hd⟩
  · exact (index_comap_of_surjective _ (f := f.middle.toMonoidHom)
      f.middle.surjective).symm.trans
        (congrArg Subgroup.index (middle_inner_preimage hCD a.extension e.middle f.middle hd))
  · exact (index_comap_of_surjective _ (f := f.middle.toMonoidHom)
      f.middle.surjective).symm.trans
        (congrArg Subgroup.index (middle_inner_preimage hCD a.extension e.middle f.middle hd))

/-- The full carrier order retains the exact original extension factor. -/
theorem SymplecticNormalizerMarking.card_eq_source {L K S : Subgroup G}
    (a : SymplecticNormalizerMarking L K S F) :
    Nat.card a.extension.carrier = Nat.card (Sp F) *
      (ChapterF.Source.parabolic ![L,K] S 0⊓ChapterF.Source.parabolic ![L,K] S 1).relIndex
        (normalizer (L : Set G)⊓normalizer (K : Set G)) := by
  rw [←a.extension.innerMap.range.card_mul_index,
    ←Nat.card_congr (MonoidHom.ofInjective a.extension.innerMap_injective).toEquiv,
    a.outer_index_eq_source]

variable [Finite G] [Finite F]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    {m : ℕ} (hm : 0<m) (hF : Nat.card F=2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (a : SymplecticNormalizerMarking L (residual H) (sourceS L H) F)
include d h hH hp hm hF he

/-- The original S=T theorem forces odd outer degree for the same carrier. -/
theorem Preparation.symplectic_extension_outer_odd :
    ¬2∣a.extension.innerMap.range.index := by
  let C := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0⊓
    ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let D := normalizer (L : Set G)⊓normalizer (residual H : Set G)
  have hTC : (T : Subgroup G)≤C := by
    rw [←d.symplectic_sourceS_eq_sylow h hH hp F hm hF he]
    exact le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left)
  have hCD : C≤D := le_inf (inf_le_left.trans a.left_le) (inf_le_right.trans a.right_le)
  have hTD : (T : Subgroup G)≤D := hTC.trans hCD
  rw [a.outer_index_eq_source]
  intro hbad
  exact (T.subtype hTD).not_dvd_index
    (hbad.trans (index_dvd_of_le (show (T.subtype hTD : Subgroup D)≤C.subgroupOf D from
      fun x hx => hTC hx)))

/-- The native unipotent subgroup is Sylow in the same full extension. -/
theorem Preparation.symplectic_extension_native_sylow :
    ∃ Q : Sylow 2 a.extension.carrier,
      (Q : Subgroup _)=(unipotent (F := F)).map a.extension.innerMap := by
  have hu : IsPGroup 2 (unipotent (F := F)) := (unipotentSylow hF hm).isPGroup'
  have hi : ¬2∣((unipotent (F := F)).map a.extension.innerMap).index := by
    rw [index_map_of_injective _ a.extension.innerMap_injective]
    exact Nat.prime_two.not_dvd_mul (unipotentSylow hF hm).not_dvd_index
      (d.symplectic_extension_outer_odd h hH hp hm hF he a)
  exact ⟨(hu.map a.extension.innerMap).toSylow hi,rfl⟩

/-- Every involution in the same full extension has a literal native lift. -/
theorem Preparation.symplectic_extension_involution_lift
    (x : a.extension.carrier) (hx : orderOf x=2) :
    ∃ v : Sp F, orderOf v=2 ∧ a.extension.innerMap v=x := by
  let E := a.extension
  let N := E.innerMap.range
  let : N.Normal := Chapter5.Section03SymplecticSource.extension_inner_range_normal E
  let q := QuotientGroup.mk' N
  have hodd : ¬2∣Nat.card (E.carrier⧸N) :=
    d.symplectic_extension_outer_odd h hH hp hm hF he a
  have hd : orderOf (q x)∣2 := by
    simpa only [hx] using orderOf_map_dvd q x
  have hqx : q x=1 := by
    apply orderOf_eq_one_iff.mp
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact h1
    · have hh := orderOf_dvd_natCard (q x)
      rw [h2] at hh
      exact (hodd hh).elim
  obtain ⟨v,hv⟩ := (QuotientGroup.eq_one_iff x).mp hqx
  refine ⟨v,?_,hv⟩
  rw [←orderOf_injective E.innerMap E.innerMap_injective,hv,hx]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
