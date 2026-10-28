module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.FullCoverMovement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightLarge
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightLarge
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSmallMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePaths
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.NonsylowImage

/-!
# Edge generation for every radical image of order eight

The marked symmetric image of the replacement radical contains an odd
permutation, by the component–radical product. Every binary subgroup of
S₆ of order eight with this property generates S₆ with a suitable conjugate
of a prescribed even involution.

For the two elementary images, use the existing point-core and three-pair
calculations. In a non-elementary image inside the canonical Sylow, its
intersection with the three-pair subgroup has order four. If this intersection
moves the last pair, the existing even-generator calculation applies.
Otherwise it is the first two-transposition plane. Short word identities
supply the adjacent transpositions, separately for the four-cycle and its
twist by the last transposition. Involution fusion transports these identities.

Lift generation through the whole two-core and the literal graph embedding.
The resulting edge kernel generates with the same prescribed endpoint actor.
No equality between the edge kernel and its relative normalizer is asserted.
EightBackward applies this result to the full endpoint restriction and excludes
its small backward image on both moving covers.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the generating choice in (5.12)(1)–(2), printed pp.924–926.
The internal imports reuse the established six-letter word calculations and
preserve their existing public boundaries.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
local notation "S" => Equiv.Perm (Fin 6)
private abbrev a : S := Equiv.swap 0 1
private abbrev b : S := Equiv.swap 2 3
private abbrev c : S := Equiv.swap 4 5
private abbrev u : S := a * (Equiv.swap 0 2 * Equiv.swap 1 3)
private abbrev r₁ : S := Equiv.swap 1 4 * Equiv.swap 3 5
private abbrev r₂ : S := Equiv.swap 1 2 * Equiv.swap 3 4

private theorem pair_four_cycle_generates (E : Subgroup S)
    (ha : a ∈ E) (hb : b ∈ E) (hu : u ∈ E) : E ⊔ zpowers r₁ = ⊤ := by
  let N := E ⊔ zpowers r₁
  have h0 : a ∈ N := mem_sup_left ha
  have h1 : b ∈ N := mem_sup_left hb
  have h2 : u ∈ N := mem_sup_left hu
  have h3 : r₁ ∈ N := mem_sup_right (mem_zpowers _)
  apply top_unique
  rw [←Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5)]
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · change Equiv.swap (0 : Fin 6) 1 ∈ N
    exact (by decide +kernel : a = Equiv.swap 0 1) ▸ h0
  · change Equiv.swap (1 : Fin 6) 2 ∈ N
    exact (by decide +kernel : r₁ * a * (u) * r₁ * a * r₁ * a * (u) * r₁ = Equiv.swap 1 2) ▸ (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem h3 h0) h2) h3) h0) h3) h0) h2) h3)
  · change Equiv.swap (2 : Fin 6) 3 ∈ N
    exact (by decide +kernel : b = Equiv.swap 2 3) ▸ h1
  · change Equiv.swap (3 : Fin 6) 4 ∈ N
    exact (by decide +kernel : a * b * (u) * r₁ * a * r₁ * (u) = Equiv.swap 3 4) ▸ (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem h0 h1) h2) h3) h0) h3) h2)
  · change Equiv.swap (4 : Fin 6) 5 ∈ N
    exact (by decide +kernel : a * r₁ * b * r₁ * (u) * r₁ * a * r₁ * a * (u) * r₁ * b * r₁ = Equiv.swap 4 5) ▸ (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem h0 h3) h1) h3) h2) h3) h0) h3) h0) h2) h3) h1) h3)

private theorem pair_twisted_cycle_generates (E : Subgroup S)
    (ha : a ∈ E) (hb : b ∈ E) (hu : u*c ∈ E) : E ⊔ zpowers r₂ = ⊤ := by
  let N := E ⊔ zpowers r₂
  have h0 : a ∈ N := mem_sup_left ha
  have h1 : b ∈ N := mem_sup_left hb
  have h2 : u*c ∈ N := mem_sup_left hu
  have h3 : r₂ ∈ N := mem_sup_right (mem_zpowers _)
  apply top_unique
  rw [←Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5)]
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · change Equiv.swap (0 : Fin 6) 1 ∈ N
    exact (by decide +kernel : a = Equiv.swap 0 1) ▸ h0
  · change Equiv.swap (1 : Fin 6) 2 ∈ N
    exact (by decide +kernel : a * r₂ * a * r₂ * a = Equiv.swap 1 2) ▸ (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem h0 h3) h0) h3) h0)
  · change Equiv.swap (2 : Fin 6) 3 ∈ N
    exact (by decide +kernel : b = Equiv.swap 2 3) ▸ h1
  · change Equiv.swap (3 : Fin 6) 4 ∈ N
    exact (by decide +kernel : a * r₂ * a * r₂ * a * r₂ = Equiv.swap 3 4) ▸ (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem h0 h3) h0) h3) h0) h3)
  · change Equiv.swap (4 : Fin 6) 5 ∈ N
    exact (by decide +kernel : r₂ * a * (u*c) * r₂ * b * r₂ * a * (u*c) * r₂ = Equiv.swap 4 5) ▸ (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem h3 h0) h2) h3) h1) h3) h0) h2) h3)

private theorem canonical_eight_even_generates (E : Subgroup S) (hES : E ≤ sylowCarrier)
    (hc : Nat.card E = 8) (hne : ¬ IsElementaryAbelian 2 E)
    (hodd : ¬ E ≤ alternatingGroup (Fin 6)) :
    ∃ r : alternatingGroup (Fin 6), orderOf r = 2 ∧ E ⊔ zpowers r.val = ⊤ := by
  by_cases hy : ∃ y ∈ E ⊓ D 6, y (4 : Fin 6) ≠ 4
  · exact ⟨⟨EightLarge.r,by decide +kernel⟩,
      orderOf_eq_prime (by decide +kernel) (by decide +kernel),
      EightLarge.canonical_even_generates E hES hne hodd hy⟩
  have hsub : E ⊓ D 6 ≤ disjointTranspositions 6 2 := by
    intro x hx
    obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) _).mp hx.2
    have hfix : dWords j (4 : Fin 6) = 4 := by
      by_contra hbad
      exact hy ⟨_,hx,hbad⟩
    have cert : ∀ j : Fin 8, dWords j (4 : Fin 6) = 4 →
        ∃ i : Fin 4, initialWords 2 i = dWords j := by decide +kernel
    exact (mem_disjointTranspositions_iff (2 : Fin 4) _).mpr (cert j hfix)
  have hCp : Nat.card (disjointTranspositions 6 2) = 4 := card_disjointTranspositions (2 : Fin 4)
  have heq : E ⊓ D 6 = disjointTranspositions 6 2 := eq_of_le_of_card_ge hsub (by
    rw [EightSmallMovers.cube_intersection_card E hES hc hne,hCp])
  have ha : a ∈ E := (show E ⊓ D 6 ≤ E from inf_le_left) (heq.symm ▸
    (show a ∈ disjointTranspositions 6 2 from
      (mem_disjointTranspositions_iff (2 : Fin 4) _).mpr ⟨1,by decide +kernel⟩))
  have hb : b ∈ E := (show E ⊓ D 6 ≤ E from inf_le_left) (heq.symm ▸
    (show b ∈ disjointTranspositions 6 2 from
      (mem_disjointTranspositions_iff (2 : Fin 4) _).mpr ⟨2,by decide +kernel⟩))
  have hex : ∃ x ∈ E, x^2 ≠ 1 := by
    by_contra! hh
    exact hne (NonsylowImage.elementary_of_squares E hh)
  obtain ⟨x,hx,hsq⟩ := hex
  obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff _).mp (hES hx)
  have hu : u ∈ E ∨ u*c ∈ E := by
    have cert : ∀ i : Fin 16, (sylowWords i)^2 ≠ 1 →
        sylowWords i=u ∨ sylowWords i=u⁻¹ ∨
        sylowWords i=u*c ∨ sylowWords i=(u*c)⁻¹ := by decide +kernel
    rcases cert i hsq with he | he | he | he
    · exact Or.inl (he ▸ hx)
    · exact Or.inl (inv_mem_iff.mp (he ▸ hx))
    · exact Or.inr (he ▸ hx)
    · exact Or.inr (inv_mem_iff.mp (he ▸ hx))
  rcases hu with hu | hu
  · exact ⟨⟨r₁,by decide +kernel⟩,
      orderOf_eq_prime (by decide +kernel) (by decide +kernel),
      pair_four_cycle_generates E ha hb hu⟩
  · exact ⟨⟨r₂,by decide +kernel⟩,
      orderOf_eq_prime (by decide +kernel) (by decide +kernel),
      pair_twisted_cycle_generates E ha hb hu⟩

private theorem eight_even_generates (E : Subgroup S) (hp : IsPGroup 2 E)
    (hc : Nat.card E = 8) (hodd : ¬ E ≤ alternatingGroup (Fin 6))
    (a₀ : alternatingGroup (Fin 6)) (hao : orderOf a₀ = 2) :
    ∃ w : S, E.map (MulAut.conj w).toMonoidHom ⊔ zpowers a₀.val = ⊤ := by
  classical
  by_cases hel : IsElementaryAbelian 2 E
  · have hne : E ≠ ⊥ := by intro he; rw [he,card_bot] at hc; omega
    obtain ⟨B,hB,hBD | hBE,hEB⟩ := exists_conjugate_le_D_or_exceptional ⟨hne,hel⟩
    · have hD : Nat.card (D 6) = 8 := card_disjointTranspositions (3 : Fin 4)
      have he : B = D 6 := eq_of_le_of_card_ge hBD (by rw [←hEB.card_eq,hc,hD])
      rw [he] at hEB
      obtain ⟨v,hv⟩ := hEB
      obtain ⟨w,hw⟩ := CubeGeneration.marked_even_generator v a₀ hao
      exact ⟨w.val,by rwa [hv]⟩
    · have he : B = exceptional 6 (by decide) := eq_of_le_of_card_ge hBE (by
        rw [←hEB.card_eq,hc,card_exceptional])
      rw [he] at hEB
      obtain ⟨v,hv⟩ := hEB
      have hpoint : pointCore = exceptional 6 (by decide) :=
        CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional
      rw [←hpoint] at hv
      obtain ⟨w,hw⟩ := PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates v a₀ hao
      exact ⟨w.val,by rwa [hv]⟩
  obtain ⟨P,hEP⟩ := hp.exists_le_sylow
  obtain ⟨v,hv⟩ := MulAction.exists_smul_eq S P sylow
  let f := (MulAut.conj v).toMonoidHom
  have hES : E.map f ≤ sylowCarrier := by
    change E.map f ≤ (sylow : Subgroup S)
    rw [←hv]
    exact map_mono hEP
  have hc' : Nat.card (E.map f) = 8 := (card_map_of_injective (MulAut.conj v).injective).trans hc
  have hn : ¬ IsElementaryAbelian 2 (E.map f) := by
    intro hh
    let := hh
    apply hel
    apply NonsylowImage.elementary_of_squares
    intro x hx
    apply (MulAut.conj v).injective
    rw [map_pow,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem f hx)
  have ho : ¬ E.map f ≤ alternatingGroup (Fin 6) := by
    intro hh
    apply hodd
    intro x hx
    have he := (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem
      (f x) (hh (mem_map_of_mem f hx)) v⁻¹
    change v⁻¹*(v*x*v⁻¹)*(v⁻¹)⁻¹ ∈ alternatingGroup (Fin 6) at he
    simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,inv_mul_cancel,mul_one] using he
  obtain ⟨r,hr,hgen⟩ := canonical_eight_even_generates (E.map f) hES hc' hn ho
  obtain ⟨k,hk⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj r a₀ hr hao)
  have he : (MulAut.conj k.val).toMonoidHom r.val = a₀.val := congrArg Subtype.val hk
  refine ⟨k.val*v,?_⟩
  have hh := congrArg (Subgroup.map (MulAut.conj k.val).toMonoidHom) hgen
  rwa [Subgroup.map_sup,CubeCommonFixer.conjugate_twice,MonoidHom.map_zpowers,he,
    map_top_of_surjective (MulAut.conj k.val).toMonoidHom (MulAut.conj k.val).surjective] at hh

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- For every radical image of order eight, the same prescribed even actor
has a generating edge kernel on the literal natural replacement graph. -/
theorem eight_generating_neighbor_of_even_actor
    (s : FullSymmetricAction h e hz hn d)
    (hcard : Nat.card (d.radical.map s.projection) = 8)
    (W : Subgroup (FreeAmalgam d.radical))
    (hWG : W ≤ stabilizer d.radical (alpha d.radical))
    (a : Equiv.Perm (Fin 6)) (ha : a ∈ (W.comap (embedM d.radical)).map s.projection)
    (hao : orderOf a = 2) (haeven : a ∈ alternatingGroup (Fin 6)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) := by
  have hodd : ¬ d.radical.map s.projection ≤ alternatingGroup (Fin 6) := by
    intro hle
    obtain ⟨x,hx⟩ := s.surjective (Equiv.swap 0 1)
    obtain ⟨k,hk,r,hr,hkr⟩ := replacement_product h d x
    have hk' : s.projection k ∈ alternatingGroup (Fin 6) := by
      rw [←s.component_image]
      exact mem_map_of_mem s.projection hk
    have hr' := hle (mem_map_of_mem s.projection hr)
    have hswap : Equiv.swap (0 : Fin 6) 1 ∈ alternatingGroup (Fin 6) := by
      rw [←hx,←hkr,map_mul]
      exact mul_mem hk' hr'
    exact (by decide : Equiv.swap (0 : Fin 6) 1 ∉ alternatingGroup (Fin 6)) hswap
  obtain ⟨k,hk⟩ := eight_even_generates (d.radical.map s.projection)
    ((replacement_radical_isPGroup h d).map s.projection) hcard hodd
      ⟨a,haeven⟩ ((Subgroup.orderOf_coe ⟨a,haeven⟩).symm.trans hao)
  obtain ⟨g,hgk⟩ := s.surjective k
  let A := W.comap (embedM d.radical)
  have hm : (d.radical.map (MulAut.conj g).toMonoidHom).map s.projection =
      (d.radical.map s.projection).map (MulAut.conj k).toMonoidHom := by
    rw [SylowCompatible.image_conjugate,hgk]
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ d.radical.map (MulAut.conj g).toMonoidHom := by
    rw [s.projection_kernel,←hQ]
    exact map_mono (replacement_core_le_radical h d)
  have hgen : d.radical.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hm,map_top_of_surjective s.projection s.surjective]
    apply top_unique
    rw [←hk]
    exact sup_le_sup_left (zpowers_le.mpr ha) _
  let f := (embedM d.radical g)⁻¹
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act d.radical f (alpha d.radical) = alpha d.radical := hf
  refine ⟨act d.radical f (beta d.radical),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff d.radical f (alpha d.radical) (beta d.radical)).mpr
      (base_adjacent d.radical)
  · have hmapA : A.map (embedM d.radical) = W :=
      map_comap_eq_self (hWG.trans_eq (stabilizer_m_base d.radical))
    have hh := congrArg (Subgroup.map (embedM d.radical)) hgen
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [Q_act,Q_beta]
    change _ = stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    have hmapR : (d.radical.map (embedM d.radical)).map (MulAut.conj f⁻¹).toMonoidHom =
        (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM d.radical x*(f⁻¹)⁻¹=embedM d.radical (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
