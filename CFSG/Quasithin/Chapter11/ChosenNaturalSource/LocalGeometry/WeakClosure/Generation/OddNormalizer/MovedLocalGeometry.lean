module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedOuter
public import Theory.GroupTheory.CentralCoprimeAbelianLift
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# The actual moved residual and its projected local normalizers

The residual is included through the original component embedding and then
projected by its center. Its full quotient by the two-core is still L/O₂(L).
Uniqueness in G controls every nontrivial two-subgroup normalized by the
projected residual: lift it to the characteristic Sylow subgroup of its
central preimage and apply uniqueness to its literal ambient image.

This is the local normalizer geometry required for the moved J₄ inspection
in Aschbacher--Smith 4.4.6--12, printed pp.620--622. It uses no C.2.8
hypothesis, and does not change the original V or discard the cubic center.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal original subgroup inside the selected component of N(A). -/
abbrev movedComponentSubgroup (A B : Subgroup G)
    (K : Subgroup (normalizer (A : Set G))) : Subgroup K :=
  (B.subgroupOf (normalizer (A : Set G))).subgroupOf K

private def componentInclusion (A : Subgroup G)
    (K : Subgroup (normalizer (A : Set G))) : K →* G :=
  (normalizer (A : Set G)).subtype.comp K.subtype

omit [Finite G] in
private theorem componentInclusion_injective (A : Subgroup G)
    (K : Subgroup (normalizer (A : Set G))) :
    Function.Injective (componentInclusion A K) :=
  (normalizer (A : Set G)).subtype_injective.comp K.subtype_injective

omit [Finite G] in
private theorem component_subgroup_le {A B : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (h : B ≤ K.map (normalizer (A : Set G)).subtype) :
    B.subgroupOf (normalizer (A : Set G)) ≤ K := by
  intro b hb
  obtain ⟨k,hk,he⟩ := h hb
  exact (Subtype.ext he : k = b) ▸ hk

omit [Finite G] in
private theorem map_component_subgroup {A B : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (h : B ≤ K.map (normalizer (A : Set G)).subtype) :
    (movedComponentSubgroup A B K).map (componentInclusion A K) = B := by
  rw [componentInclusion,←map_map,map_subgroupOf_eq_of_le (component_subgroup_le K h),
    map_subgroupOf_eq_of_le (h.trans (map_subtype_le _))]

/-- The projected residual retains the full covering quotient. -/
theorem moved_projected_cover (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A)) (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    let X := (movedComponentSubgroup A (oddActorResidual L A) K).map
      (QuotientGroup.mk' (center K))
    Group.IsPerfect X ∧ Nonempty ((X ⧸ pCore 2 X) ≃* (L ⧸ pCore 2 L)) := by
  let N := normalizer (A : Set G)
  let F := oddActorResidual L A
  let Y := movedComponentSubgroup A F K
  let q := QuotientGroup.mk' (center K)
  have hFN : F ≤ N := hFK.trans (map_subtype_le _)
  let ef : Y ≃* F := (subgroupOfEquivOfLe (component_subgroup_le K hFK)).trans
    (subgroupOfEquivOfLe hFN)
  let j : F →* K := Y.subtype.comp ef.symm.toMonoidHom
  have hj : Function.Injective j := Y.subtype_injective.comp ef.symm.injective
  let f := q.comp j
  have hcentral : f.ker ≤ center F := by
    intro b hb
    apply mem_center_iff.mpr
    intro c
    apply hj
    simpa only [map_mul] using
      (mem_center_iff.mp ((QuotientGroup.eq_one_iff (j b)).mp hb)) (j c)
  have hFL : F ≤ L := (oddActorResidual_le L A).trans inf_le_left
  obtain ⟨hc,_,hVcore,_⟩ := actor_cover D S hA hodd
  have hVF : V ≤ F := hVcore.trans (pCoreIn_le 2 F)
  have hker : f.ker ≤ (L.pCoreIn 2).comap F.subtype := by
    intro b hb
    apply (centralizer_eq_core D S).le
    refine ⟨hFL b.property,?_⟩
    intro v hv
    exact congrArg Subtype.val ((mem_center_iff.mp (hcentral hb)) ⟨v,hVF hv⟩)
  have hk : IsPGroup 2 f.ker := ((isPGroup_pCoreIn 2 L).comap_subtype).to_le hker
  have hrange : f.range = Y.map q := by
    change (q.comp (Y.subtype.comp ef.symm.toMonoidHom)).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr ef.symm.surjective,←MonoidHom.range_eq_map,
      range_subtype]
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  have hp : Group.IsPerfect f.range := Group.IsPerfect.range f
  obtain ⟨e,_⟩ := actor_cover_quotient D S hA hodd
  have he : Nonempty ((f.range ⧸ pCore 2 f.range) ≃* (L ⧸ pCore 2 L)) :=
    ⟨(f.rangeRestrict.quotientPCoreEquivOfSurjective f.rangeRestrict_surjective
      (by rw [MonoidHom.ker_rangeRestrict]; exact hk)).symm.trans e⟩
  rw [hrange] at hp he
  exact ⟨hp,he⟩

private theorem central_two_subgroup_lift
    {H Q : Type*} [Group H] [Finite H] [Group Q] [Finite Q]
    (f : H →* Q) (hf : Function.Surjective f) (hc : f.ker ≤ center H)
    (B : Subgroup Q) (hB : IsPGroup 2 B) :
    ∃ P : Subgroup H, IsPGroup 2 P ∧ P.map f = B ∧
      (normalizer (B : Set Q)).comap f ≤ normalizer (P : Set H) := by
  let R := B.comap f
  let g : R →* B := f.subgroupComap B
  have hg : Function.Surjective g := f.subgroupComap_surjective_of_surjective B hf
  have hgc : g.ker ≤ center R := by
    intro x hx
    have hxk : (x : H) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hc hxk) y)
  let : Group.IsNilpotent B := hB.isNilpotent
  let : Group.IsNilpotent R := Subgroup.isNilpotent_of_ker_le_center g hgc
  let P : Sylow 2 R := Sylow.nonempty.some
  let : (P : Subgroup R).Characteristic := P.characteristic_of_normal inferInstance
  have hPtop : (P.mapSurjective hg : Subgroup B) = ⊤ := by
    apply top_unique
    exact (hB.to_subgroup ⊤).le_sylow_of_normal _
  have hm : ((P : Subgroup R).map R.subtype).map f = B := by
    have hh := congrArg (Subgroup.map B.subtype) hPtop
    change ((P : Subgroup R).map g).map B.subtype = (⊤ : Subgroup B).map B.subtype at hh
    rw [map_map,←MonoidHom.range_eq_map,range_subtype] at hh
    change (P : Subgroup R).map (f.comp R.subtype) = B at hh
    simpa only [map_map] using hh
  refine ⟨(P : Subgroup R).map R.subtype,P.isPGroup'.map _,hm,?_⟩
  exact (le_of_eq (comap_normalizer_eq_of_surjective B hf)).trans
    (normalizer_le_normalizer_characteristic_image R (P : Subgroup R))

/-- Every actual projected two-local normalized by the residual normalizes it.
This is transported from its unique maximal two-local overgroup in G. -/
theorem moved_projected_two_normalizer
    {A : Subgroup G}
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    let X := (movedComponentSubgroup A (oddActorResidual L A) K).map
      (QuotientGroup.mk' (center K))
    ∀ B : Subgroup (K ⧸ center K), IsPGroup 2 B → B ≠ ⊥ →
      X ≤ normalizer (B : Set (K ⧸ center K)) →
      normalizer (B : Set (K ⧸ center K)) ≤ normalizer (X : Set (K ⧸ center K)) := by
  let F := oddActorResidual L A
  let Y := movedComponentSubgroup A F K
  let q := QuotientGroup.mk' (center K)
  let j := componentInclusion A K
  dsimp only
  intro B hB hne hXB
  obtain ⟨P,hP,hPB,hnP⟩ := central_two_subgroup_lift q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) B hB
  have hYP : Y ≤ normalizer (P : Set K) := by
    intro y hy
    exact hnP (hXB (mem_map_of_mem q hy))
  have hneP : P ≠ ⊥ := by
    intro hz
    rw [hz,Subgroup.map_bot] at hPB
    exact hne hPB.symm
  have hFP : F ≤ normalizer (P.map j : Set G) := by
    change oddActorResidual L A ≤ _
    rw [←map_component_subgroup K hFK]
    exact (map_mono hYP).trans (P.le_normalizer_map j)
  have hcontrol : normalizer (P.map j : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal hu.2.2 (hP.map j)
      (fun hz => hneP ((map_eq_bot_iff_of_injective P (componentInclusion_injective A K)).mp hz)) hFP
  have hPN : normalizer (P : Set K) ≤ normalizer (Y : Set K) := by
    rw [←subgroupOf_normalizer_eq (component_subgroup_le K hFK),
      ←subgroupOf_normalizer_eq (hFK.trans (map_subtype_le _))]
    intro k hk
    apply normalizes_oddActorResidual L A
    exact ⟨hcontrol (P.le_normalizer_map j (mem_map_of_mem j hk)),k.val.property⟩
  intro b hb
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (center K) b
  exact Y.le_normalizer_map q (mem_map_of_mem q (hPN (hnP hb)))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
