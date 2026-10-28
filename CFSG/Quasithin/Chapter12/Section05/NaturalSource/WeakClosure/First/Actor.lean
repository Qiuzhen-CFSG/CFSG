module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Geometry
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.FlagSylow
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.AmalgamLocalCores

/-!
# The literal L₆ and R₆ actor images

The LT actor kernel is a two-group: its intersection with L is the kernel
O₂(L) of the original quotient marking, and LT/L is a two-group. Thus the
preimage of the full flag group is T by Sylow maximality. Equivariance
identifies the image of N_L(V₆) with the four-space parabolic. Surjective
transport of the solvable residual identifies the image of L₆; transport
of the two-core identifies the image of the original R₆ = O₂(L₆T).

Source: Aschbacher--Smith, notation before 12.5.2 and the last step of
12.5.10(1), printed pp.817,821. All normality is relative to the indicated
local subgroup, and all maps extend the original chosen-module quotient.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource.SylowExteriorMarking
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section05.NaturalSource
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
variable (s : SylowExteriorMarking D)

theorem actor_restrict_ker :
    (s.actor.comp (inclusion (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))).ker = pCore 2 L := by
  ext l
  change s.actor ⟨(l : G), (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) l.property⟩ = 1 ↔
    l ∈ pCore 2 L
  rw [s.actor_component, map_eq_one_iff _ s.marking.quotientEquiv.injective]
  exact QuotientGroup.eq_one_iff l

theorem actor_kernel_isPGroup : IsPGroup 2 s.actor.ker := by
  let M := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf M
  let _ : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hgen : N ⊔ (T : Subgroup G).subgroupOf M = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  have hquot : IsPGroup 2 (M ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf M)
      T.isPGroup'.comap_subtype hgen
  let q := (QuotientGroup.mk' N).comp s.actor.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* L :=
      (M.subtype.comp (s.actor.ker.subtype.comp q.ker.subtype)).codRestrict L (by
        intro x
        change x.val.val ∈ N
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 L := by
      intro x
      exact (actor_restrict_ker s).le x.val.property
    let r' : q.ker →* pCore 2 L := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 L => (x.val : G)) hab
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

theorem actor_preimage_flag_eq_sylow :
    ((SL5ExteriorSquare.flagGroup.comap s.actor).map
      (L ⊔ (T : Subgroup G)).subtype) = (T : Subgroup G) := by
  have hflag : IsPGroup 2 SL5ExteriorSquare.flagGroup := by
    rw [SL5ExteriorSquare.flagGroup_eq_standardBorel_comap]
    exact BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardSylow.isPGroup'.comap_of_injective
      (BinaryLinear.OuterCyclic.slEquivLinear 5).toMonoidHom
      (BinaryLinear.OuterCyclic.slEquivLinear 5).injective
  apply T.is_maximal' ((hflag.comap_of_ker_isPGroup s.actor
    (actor_kernel_isPGroup s)).map (L ⊔ (T : Subgroup G)).subtype)
  intro t ht
  exact ⟨⟨t, (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) ht⟩,
    s.sylow_flag ⟨t, ht⟩, rfl⟩

theorem mem_normalizer_subspace_iff (h : (L ⊔ (T : Subgroup G) : Subgroup G))
    (W : Submodule (ZMod 2) SL5ExteriorSquare.V) :
    (h : G) ∈ normalizer (s.marking.subspace W : Set G) ↔
      s.actor h ∈ SL5ExteriorSquare.exteriorStabilizer W := by
  rw [mem_normalizer_iff]
  constructor
  · intro hn w
    let v := s.marking.coordinates.symm (Multiplicative.ofAdd w)
    have hv : (s.marking.coordinates v).toAdd = w := by
      simp only [v, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have he := s.equivariant h v
    have hh := hn (v : G)
    rw [s.marking.mem_subspace W v,
      s.marking.mem_subspace W ⟨(h : G) * v * (h : G)⁻¹,
        (mem_normalizer_iff.mp (s.normalizes h.property) v).mp v.property⟩,
      he, toAdd_ofAdd, hv] at hh
    exact hh.symm
  · intro hn v
    constructor
    · intro hv
      have hvV := s.marking.subspace_le W hv
      have he := s.equivariant h ⟨v, hvV⟩
      apply (s.marking.mem_subspace W ⟨(h : G) * v * (h : G)⁻¹,
        (mem_normalizer_iff.mp (s.normalizes h.property) v).mp hvV⟩).mpr
      rw [he]
      exact (hn _).mpr ((s.marking.mem_subspace W ⟨v, hvV⟩).mp hv)
    · intro hv
      have hvV : v ∈ V := (mem_normalizer_iff.mp (s.normalizes h.property) v).mpr
        (s.marking.subspace_le W hv)
      apply (s.marking.mem_subspace W ⟨v, hvV⟩).mpr
      apply (hn _).mp
      have hh := (s.marking.mem_subspace W ⟨(h : G) * v * (h : G)⁻¹,
        (mem_normalizer_iff.mp (s.normalizes h.property) v).mp hvV⟩).mp hv
      rwa [s.equivariant h ⟨v, hvV⟩] at hh

def localSixActor : (L ⊓ s.marking.Gi 6 : Subgroup G) →* SL5ExteriorSquare.parabolic 4 :=
  (s.actor.comp (inclusion (inf_le_left.trans le_sup_left))).codRestrict _ (by
    intro l
    rw [← SL5ExteriorSquare.exteriorStabilizer_V₆_eq_parabolic]
    exact (mem_normalizer_subspace_iff s _ _).mp l.property.2)

theorem localSixActor_surjective : Function.Surjective (localSixActor s) := by
  intro g
  obtain ⟨q, hq⟩ := s.marking.quotientEquiv.surjective (g : SL5TenDimensional.Group)
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  have ha : s.actor ⟨l, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) l.property⟩ = g := by
    rw [s.actor_component, hl, hq]
  have hn : (l : G) ∈ s.marking.Gi 6 := by
    apply (mem_normalizer_subspace_iff s
      ⟨(l : G), (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) l.property⟩
      SL5ExteriorSquare.V₆).mpr
    rw [ha, SL5ExteriorSquare.exteriorStabilizer_V₆_eq_parabolic]
    exact g.property
  exact ⟨⟨l, l.property, hn⟩, Subtype.ext ha⟩

theorem actorImage_L₆ [Finite G] :
    s.actorImage (s.marking.Li 6) = SL5ExteriorSquare.parabolic 4 := by
  have he := map_solvableResidual_eq (localSixActor s) (localSixActor_surjective s)
  rw [solvableResidual_eq_top (G := SL5ExteriorSquare.parabolic 4)] at he
  have hh := congrArg (fun A : Subgroup (SL5ExteriorSquare.parabolic 4) =>
    A.map (SL5ExteriorSquare.parabolic 4).subtype) he
  rw [map_map, ← MonoidHom.range_eq_map, range_subtype] at hh
  rw [← hh]
  ext x
  constructor
  · rintro ⟨l, ⟨k, hk, hkl⟩, rfl⟩
    exact ⟨k, hk, congrArg s.actor (Subtype.ext hkl)⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k, (show L ⊓ s.marking.Gi 6 ≤ L ⊔ (T : Subgroup G) from
      inf_le_left.trans le_sup_left) k.property⟩, ?_, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem actorImage_sup {A B : Subgroup G}
    (hA : A ≤ L ⊔ (T : Subgroup G)) (hB : B ≤ L ⊔ (T : Subgroup G)) :
    s.actorImage (A ⊔ B) = s.actorImage A ⊔ s.actorImage B := by
  unfold SylowExteriorMarking.actorImage
  rw [subgroupOf_sup hA hB, Subgroup.map_sup]

theorem actorImage_R₆ [Finite G] : s.actorImage (s.marking.Ri 6) =
    SL5ExteriorSquare.parabolicResidualTwoCore 4 := by
  let H := L ⊔ (T : Subgroup G)
  let Y := s.marking.Li 6 ⊔ (T : Subgroup G)
  have hY : Y ≤ H := sup_le ((s.marking.Li_le_L 6).trans le_sup_left) le_sup_right
  have hI : s.actorImage Y = SL5ExteriorSquare.parabolic 4 := by
    rw [actorImage_sup s ((s.marking.Li_le_L 6).trans le_sup_left) le_sup_right,
      actorImage_L₆ s]
    exact sup_eq_left.mpr ((s.actorImage_le_flag le_rfl).trans
      (SL5ExteriorSquare.flagGroup_le_parabolic 4 (by decide)))
  have hR : (Y.pCoreIn 2).subgroupOf H = (Y.subgroupOf H).pCoreIn 2 := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 Y).trans hY),
      ← AmalgamLocalCores.pCoreIn_map_of_injective 2 H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hY]
  change ((Y.pCoreIn 2).subgroupOf H).map s.actor = _
  rw [hR, map_pCoreIn_of_ker_isPGroup s.actor (actor_kernel_isPGroup s)]
  change (s.actorImage Y).pCoreIn 2 = _
  rw [hI]
  change _ = (SL5ExteriorSquare.parabolicResidualFlag 4).pCoreIn 2
  rw [SL5ExteriorSquare.parabolicResidualFlag_four]

end CFSG.Quasithin.Chapter12.Section05.NaturalSource.SylowExteriorMarking
