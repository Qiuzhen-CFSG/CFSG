module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Solvable

import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# A complement in the original selected two-residual

The solvable branch of B.6.8 identifies the image of O²(H) in H/O₂(H)
with an odd prime core. Lift a Sylow subgroup through the restricted
quotient map. Its image is a subgroup P of the original residual, and
its disjointness from O₂(H) makes the restricted map an isomorphism.
The two-core of the residual is its intersection with O₂(H), giving
the complementary product. The star-quotient disjointness and the
Frattini identity in H/O₂(H) then give P∩M=Φ(P). All these identities
are transported along the literal inclusion H→G.

Source: Aschbacher--Smith B.6.8(2), printed pp.113--114, as used in
11.5.7, printed p.782. The internal Structure import unfolds the
minimal-parabolic normal core inside the proof; no public boundary changes.
-/

public section
open Subgroup
open CFSG.Quasithin
noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
open CFSG.Quasithin.Chapter12.Section02

private theorem frattini_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  apply le_antisymm
  · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro b hb
    exact ⟨e.symm b,frattini_le_comap_frattini_of_surjective
      (φ := e.symm.toMonoidHom) e.symm.surjective hb,e.apply_symm_apply b⟩

private theorem intrinsic_complement {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (hmin : ChapterB.IsMinimalParabolicOver S ⊤)
    (hs : Group.IsSolvable H) :
    ∃ (p : ℕ) (P : Subgroup H), p.Prime ∧ Odd p ∧ IsPGroup p P ∧
      P ≤ pResidual 2 H ∧ P ≠ ⊥ ∧
      pResidual 2 H = (pResidual 2 H).pCoreIn 2 ⊔ P ∧
      Disjoint ((pResidual 2 H).pCoreIn 2) P ∧
      P ⊔ (S : Subgroup H) = ⊤ ∧
      P ⊓ ChapterB.minimalParabolicMax S hmin = (frattini P).map P.subtype := by
  obtain ⟨p,hp,ho,hRbar,_,hPhi,_,_⟩ :=
    ChapterB.minimalParabolic_solvable_structure S hmin hs
  let : Fact p.Prime := ⟨hp⟩
  let R := pResidual 2 H
  let Q := pCore 2 H
  let q := QuotientGroup.mk' Q
  let B := R.map q
  have hB : B = pCore p (H ⧸ Q) := by
    rw [show B = R.map q from rfl, map_pResidual_of_surjective 2 q
      (QuotientGroup.mk'_surjective Q)]
    exact hRbar
  have hBp : IsPGroup p B := hB.symm ▸ pCore_isPGroup
  let f := q.subgroupMap R
  let U : Sylow p R := Sylow.nonempty.some
  have hUtop : (U.mapSurjective (q.subgroupMap_surjective R) : Subgroup B) = ⊤ :=
    top_unique ((hBp.to_subgroup ⊤).le_sylow_of_normal _)
  let P := (U : Subgroup R).map R.subtype
  have hPR : P ≤ R := map_subtype_le _
  have hPp : IsPGroup p P := U.isPGroup'.map R.subtype
  have hdis : Disjoint Q P := pCore_isPGroup.disjoint_of_coprime hPp
    (Nat.coprime_two_left.mpr ho)
  have hPmap : P.map q = B := by
    apply le_antisymm (map_mono hPR)
    rintro b ⟨r,hr,rfl⟩
    have ht : (⟨q r,mem_map_of_mem q hr⟩ : B) ∈
        (U.mapSurjective (q.subgroupMap_surjective R) : Subgroup B) := by
      rw [hUtop]; exact mem_top _
    obtain ⟨u,hu,he⟩ := ht
    exact ⟨u,mem_map_of_mem R.subtype hu,congrArg Subtype.val he⟩
  have hcore : R.pCoreIn 2 = R ⊓ Q := by
    apply le_antisymm
    · refine le_inf (pCoreIn_le 2 R) ?_
      change (pCore 2 R).map R.subtype ≤ Q
      exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map R.subtype⟩
    · have hl : Q.subgroupOf R ≤ pCore 2 R :=
        le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
      simpa only [subgroupOf_map_subtype, inf_comm,pCoreIn] using map_mono (f := R.subtype) hl
  have hcover : R = R.pCoreIn 2 ⊔ P := by
    rw [hcore]
    apply le_antisymm _ (sup_le inf_le_left hPR)
    intro r hr
    obtain ⟨a,ha,he⟩ := hPmap.ge (mem_map_of_mem q hr)
    have hk : r / a ∈ Q := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (r / a) = 1
      rw [map_div,he,div_self']
    have hm := (R ⊓ Q ⊔ P).mul_mem
      (mem_sup_left ⟨R.div_mem hr (hPR ha),hk⟩) (mem_sup_right ha)
    simpa only [div_mul_cancel] using hm
  have hgen : P ⊔ (S : Subgroup H) = ⊤ := by
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top S]
    apply sup_le _ le_sup_right
    rw [show pResidual 2 H = R from rfl,hcover]
    exact sup_le ((hcore.le.trans inf_le_right).trans
      ((pCore_isPGroup.le_sylow_of_normal S).trans le_sup_right)) le_sup_left
  have hne : P ≠ ⊥ := by
    intro he
    have ht : (S : Subgroup H) = ⊤ := by simpa only [he,bot_sup_eq] using hgen
    exact (ChapterB.minimalParabolicMax_spec S hmin).1.ne_top
      (top_unique (ht ▸ (ChapterB.minimalParabolicMax_spec S hmin).2))
  have hi : Function.Injective (q.subgroupMap P) := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    apply Subtype.ext
    apply disjoint_def.mp hdis
    · exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val ha)
    · exact a.property
  let e : P ≃* P.map q := MulEquiv.ofBijective (q.subgroupMap P)
    ⟨hi,q.subgroupMap_surjective P⟩
  have hphimap : ((frattini P).map P.subtype).map q =
      (frattini (P.map q)).map (P.map q).subtype := by
    rw [← frattini_map_equiv e,map_map,map_map]
    rfl
  have hphibar : ((frattini P).map P.subtype).map q =
      (ChapterB.minimalParabolicCore S hmin).map q := by
    rw [hphimap,hPmap,hB]
    exact hPhi.symm
  have hQJ : Q ≤ ChapterB.minimalParabolicCore S hmin :=
    ChapterB.minimalParabolicTwoCore_le_core S hmin
  have hRM : R ⊓ ChapterB.minimalParabolicMax S hmin ≤
      ChapterB.minimalParabolicCore S hmin := by
    obtain ⟨_,_,_,_,_,hdisstar⟩ :=
      ChapterB.minimalParabolic_solvable_star_structure S hmin hs
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply mem_bot.mp
    rw [← hdisstar]
    exact ⟨map_pResidual_le 2 (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hmin))
      (mem_map_of_mem _ hx.1),mem_map_of_mem _ hx.2⟩
  have hphi : P ⊓ ChapterB.minimalParabolicMax S hmin =
      (frattini P).map P.subtype := by
    apply le_antisymm
    · intro a ha
      have haj := hRM ⟨hPR ha.1,ha.2⟩
      obtain ⟨b,hb,he⟩ := hphibar.ge (mem_map_of_mem q haj)
      have hab : (⟨a,ha.1⟩ : P) = ⟨b,map_subtype_le _ hb⟩ := by
        apply hi
        exact Subtype.ext he.symm
      have heba : b = a := (congrArg Subtype.val hab).symm
      rwa [heba] at hb
    · intro a ha
      have hap := map_subtype_le _ ha
      have haj : a ∈ ChapterB.minimalParabolicCore S hmin := by
        have hm := hphibar.le (mem_map_of_mem q ha)
        have hc : a ∈ ((ChapterB.minimalParabolicCore S hmin).map q).comap q := hm
        rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hQJ] at hc
        exact hc
      exact ⟨hap,normalCore_le _ haj⟩
  exact ⟨p,P,hp,ho,hPp,hPR,hne,hcover,hdis.mono_left (hcore.le.trans inf_le_right),hgen,hphi⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

/-- The actual odd complement in the original selected residual, including
its Frattini intersection with the original maximal overgroup. -/
theorem exists_residual_complement
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hNT : normalizer (T : Set G) ≤ E.M) (hs : Group.IsSolvable E.H) :
    ∃ (p : ℕ) (P : Subgroup G), p.Prime ∧ Odd p ∧ IsPGroup p P ∧
      P ≤ outsideResidual E ∧ P ≠ ⊥ ∧
      outsideResidual E = (outsideResidual E).pCoreIn 2 ⊔ P ∧
      Disjoint ((outsideResidual E).pCoreIn 2) P ∧
      P ⊔ (T : Subgroup G) = E.H ∧
      P ⊓ E.M = (frattini P).map P.subtype := by
  obtain ⟨hmin,hmax⟩ := selected_minimal_parabolic E hH hNT
  obtain ⟨p,P₀,hp,ho,hP,hPR,hne,hcover,hdis,hgen,hPhi⟩ :=
    intrinsic_complement (T.subtype hH.1.1.2) hmin hs
  let P := P₀.map E.H.subtype
  let he : P₀ ≃* P := Subgroup.equivMapOfInjective P₀ E.H.subtype E.H.subtype_injective
  have hneP : P ≠ ⊥ := by
    intro hz
    apply hne
    apply map_injective E.H.subtype_injective
    simpa only [Subgroup.map_bot] using hz
  have hc : outsideResidual E = (outsideResidual E).pCoreIn 2 ⊔ P := by
    have hh := congrArg (map E.H.subtype) hcover
    rw [Subgroup.map_sup,map_pCoreIn_of_injective 2 _ _ E.H.subtype_injective] at hh
    exact hh
  have hd : Disjoint ((outsideResidual E).pCoreIn 2) P := by
    rw [show (outsideResidual E).pCoreIn 2 =
      ((pResidual 2 E.H).pCoreIn 2).map E.H.subtype from
        (map_pCoreIn_of_injective 2 _ _ E.H.subtype_injective).symm]
    exact disjoint_map E.H.subtype_injective hdis
  have hg : P ⊔ (T : Subgroup G) = E.H := by
    have hh := congrArg (map E.H.subtype) hgen
    rw [Subgroup.map_sup,← MonoidHom.range_eq_map,range_subtype] at hh
    have hST : ((T.subtype hH.1.1.2 : Sylow 2 E.H) : Subgroup E.H).map E.H.subtype =
        (T : Subgroup G) := by
      change ((T : Subgroup G).subgroupOf E.H).map E.H.subtype = _
      exact map_subgroupOf_eq_of_le hH.1.1.2
    rw [hST] at hh
    exact hh
  have hf : P ⊓ E.M = (frattini P).map P.subtype := by
    have hh := congrArg (map E.H.subtype) hPhi
    rw [hmax,map_inf _ _ _ E.H.subtype_injective,subgroupOf_map_subtype] at hh
    have hleft : P ⊓ (E.M ⊓ E.H) = P ⊓ E.M := by
      rw [← inf_assoc,inf_eq_left.mpr (inf_le_left.trans (map_subtype_le _))]
    rw [hleft] at hh
    rw [hh,← frattini_map_equiv he,map_map,map_map]
    rfl
  exact ⟨p,P,hp,ho,hP.map E.H.subtype,map_mono hPR,hneP,hc,hd,hg,hf⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
