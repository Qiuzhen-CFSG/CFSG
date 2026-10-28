module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSixDegree.Reduction
public import Theory.Alternating.TripleSixActorGeneration
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Inner elementary actors for the triple-A₆ degree bound

The odd coordinate kernel embeds every elementary two-subgroup in A₆,
whose dihedral Sylow subgroup gives rank at most two. Three conjugates of
an involution generate the alternating quotient; perfectness lifts this
generation through the central kernel. The final containment keeps the
original component inclusion and actual ambient conjugators.

Source: Aschbacher–Smith K.1–K.1.3, printed pp.452–453.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Atlas.Codes

namespace CFSG.Quasithin.ChapterK.Alternating.TripleSixReduction

private theorem hexEven_elementary_card (E : Subgroup HexEvenAutomorphisms)
    (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 4 := by
  let := hE
  let P : Sylow 2 (alternatingGroup (Fin 6)) := Sylow.nonempty.some
  obtain ⟨d⟩ := AlternatingSix.ShadowLocal.alternatingSylow_dihedral P
  have hr : primeRank 2 (alternatingGroup (Fin 6)) ≤ 2 := by
    rw [P.primeRank_eq, primeRank_equiv 2 d]
    exact dihedral_rank_le_two 2
  have hf := injective_comp_subtype_of_coprime_ker hexEvenCoordinate
    (by rw [hexEven_kernel_card]; decide : Nat.Coprime 2 (Nat.card hexEvenCoordinate.ker))
    E (IsElementaryAbelian.isPGroup 2 E)
  let f := hexEvenCoordinate.comp E.subtype
  have hEf : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).le.trans
    ((primeRank_le_iff_elementary_card_le _).mp hr f.range hEf)

private theorem hexEven_three_conjugates (t : HexEvenAutomorphisms)
    (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ g h : HexEvenAutomorphisms,
      zpowers t ⊔ zpowers (g * t * g⁻¹) ⊔ zpowers (h * t * h⁻¹) = ⊤ := by
  let := Hexacode.even_isPerfect
  let q := hexEvenCoordinate
  have hqt : q t ≠ 1 := by
    intro he
    have htker : t ∈ q.ker := he
    have hthree : t ^ 3 = 1 := by
      have h := pow_card_eq_one' (x := (⟨t, htker⟩ : q.ker))
      rw [hexEven_kernel_card] at h
      exact congrArg Subtype.val h
    have heq : t ^ 3 = t := by rw [pow_succ, ht2, one_mul]
    exact ht (heq.symm.trans hthree)
  obtain ⟨g, h, hgen⟩ := alternatingGroup.TripleSixActorGeneration.three_conjugates_generate
    (q t) hqt (by rw [← map_pow, ht2, map_one])
  obtain ⟨g', rfl⟩ := hexEvenCoordinate_surjective g
  obtain ⟨h', rfl⟩ := hexEvenCoordinate_surjective h
  refine ⟨g', h', ?_⟩
  let J := zpowers t ⊔ zpowers (g' * t * g'⁻¹) ⊔ zpowers (h' * t * h'⁻¹)
  have hmap : J.map q = ⊤ := by
    simpa only [J, Subgroup.map_sup, MonoidHom.map_zpowers, map_mul, map_inv] using hgen
  have hs : Function.Surjective (q.comp J.subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    exact hmap
  have hj := PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    q J.subtype hs (Hexacode.even_kernel_eq_center.le)
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := hj x
  exact y.property

variable {G : Type*} [Group G] {L A : Subgroup G}

/-- Every nontrivial inner elementary actor has the required actual generating triple. -/
theorem actorGeometry_of_le (e : L ≃* HexEvenAutomorphisms)
    (hA : IsElementaryTwo A) (hAL : A ≤ L) : ActorGeometry e A := by
  let := hA.2
  let f : A →* HexEvenAutomorphisms := e.toMonoidHom.comp (inclusion hAL)
  have hf : Function.Injective f := e.injective.comp (inclusion_injective hAL)
  have hcard : Nat.card A ≤ 4 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).le.trans
      (hexEven_elementary_card f.range
        (IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective))
  have hr : rank A ≤ 2 := by
    have hh := Nat.log_mono_right (b := 2) hcard
    exact hh
  obtain ⟨t, htA, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let tL : L := ⟨t, hAL htA⟩
  have htL : tL ≠ 1 := fun he => ht1 (congrArg Subtype.val he)
  have ht2 : tL ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian t htA)
  obtain ⟨g, h, hgen⟩ := hexEven_three_conjugates (e tL)
    (fun he => htL (e.injective (he.trans (map_one e).symm)))
    (by rw [← map_pow, ht2, map_one])
  have hgenL : zpowers tL ⊔ zpowers (e.symm g * tL * (e.symm g)⁻¹) ⊔
      zpowers (e.symm h * tL * (e.symm h)⁻¹) = ⊤ := by
    have hh := congrArg (Subgroup.map e.symm.toMonoidHom) hgen
    simpa only [Subgroup.map_sup, MonoidHom.map_zpowers, map_mul, map_inv,
      MulEquiv.coe_toMonoidHom, e.symm_apply_apply,
      Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] using hh
  refine ⟨t, htA, ht1, Or.inl ⟨hr, ![1, (e.symm g : G), (e.symm h : G)], ?_⟩⟩
  let J : Subgroup G := closure (Set.range fun i : Fin 3 =>
    (![1, (e.symm g : G), (e.symm h : G)] i) * t *
      (![1, (e.symm g : G), (e.symm h : G)] i)⁻¹)
  have htJ : t ∈ J := by
    simpa using (subset_closure (Set.mem_range_self (0 : Fin 3)) :
      (![1, (e.symm g : G), (e.symm h : G)] 0) * t *
        (![1, (e.symm g : G), (e.symm h : G)] 0)⁻¹ ∈ J)
  have hgJ : (e.symm g : G) * t * (e.symm g : G)⁻¹ ∈ J :=
    subset_closure (Set.mem_range_self (1 : Fin 3))
  have hhJ : (e.symm h : G) * t * (e.symm h : G)⁻¹ ∈ J :=
    subset_closure (Set.mem_range_self (2 : Fin 3))
  have hle : zpowers tL ⊔ zpowers (e.symm g * tL * (e.symm g)⁻¹) ⊔
      zpowers (e.symm h * tL * (e.symm h)⁻¹) ≤ J.comap L.subtype :=
    sup_le (sup_le (zpowers_le.mpr htJ) (zpowers_le.mpr hgJ)) (zpowers_le.mpr hhJ)
  rw [hgenL] at hle
  intro l hl
  exact hle (mem_top (⟨l, hl⟩ : L))

end CFSG.Quasithin.ChapterK.Alternating.TripleSixReduction
