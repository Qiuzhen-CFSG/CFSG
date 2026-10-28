module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.HigmanSimsOddRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RudvalisOddRank

/-!
# Quasisimple point quotients in the sporadic containing rows

The original point quotient is SQTK and has a top C-component. In the
noncentral Fitting branch, A.3.6 forces either a prime cube or the product
120 p² in its order, for p > 3. The certified orders exclude this in J₁,
J₂, M₂₂, its triple cover and M₂₃. Both positive homocyclic exponents and
the actual covering center are retained.

More generally a nonquasisimple point quotient has rank at least two at
some prime greater than three: a cyclic noncentral prime core would be
centralized by the perfect point quotient. The native full-Sylow overgroup
bounds in HS and Ru exclude this rank. All comparisons pass through the
literal point image and its intrinsic two-core quotient.

The chosen-flag consumer also derives field four from the complete
containing catalogue. This removes the nonquasisimple point branches in
seven sporadic rows; their quasisimple pair comparisons, the J₄ row and
final component equality remain with qt-d-1222-shadow-component-comparison.
The earlier geometry retains final discharge by qt-d-1222-shadow-components.
Source: Aschbacher--Smith A.3.6, A.3.12 and 11.4.2, printed pp.43--48,776.
Imported sporadic carrier calculations retain LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open Chapter1.Section02 Chapter1.Section02.LocalModels

private def sporadicOrderBound : ℕ := 2^7 * 3^3 * 5^2 * 7 * 11 * 19 * 23

private theorem large_prime_divisor {p : ℕ} (hp : p.Prime) (hl : 3 < p)
    (hd : p ∣ sporadicOrderBound) : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 ∨ p = 23 := by
  unfold sporadicOrderBound at hd
  simp only [hp.dvd_mul, or_assoc] at hd
  rcases hd with h | h | h | h | h | h | h
  · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h; omega
  · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three h; omega
  · exact .inl (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_five h)
  · exact .inr (.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
  · exact .inr (.inr (.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)))
  · exact .inr (.inr (.inr (.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))))
  · exact .inr (.inr (.inr (.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))))

private theorem no_natural_order {p : ℕ} (hp : p.Prime) (hl : 3 < p) :
    ¬ p^3 ∣ sporadicOrderBound := by
  intro hd
  have h := large_prime_divisor hp hl ((dvd_pow_self p (by decide : 3 ≠ 0)).trans hd)
  rcases h with rfl | rfl | rfl | rfl | rfl <;> norm_num [sporadicOrderBound] at hd

private theorem no_nilpotent_order {p : ℕ} (hp : p.Prime) (hl : 3 < p) :
    ¬ p^2 * 120 ∣ sporadicOrderBound := by
  intro hd
  have h := large_prime_divisor hp hl
    ((dvd_mul_of_dvd_left (dvd_pow_self p (by decide : 2 ≠ 0)) 120).trans hd)
  rcases h with rfl | rfl | rfl | rfl | rfl <;> norm_num [sporadicOrderBound] at hd

private theorem quasisimple_of_sporadic_order
    {A : Type*} [Group A] [Finite A]
    (hsq : IsSQTK KnownSimple.IsKnownSimple A) (hO : pCore 2 A = ⊥)
    {C : Subgroup A} (hC : C.IsCComponent) (hd : Nat.card C ∣ sporadicOrderBound) :
    IsQuasisimple C := by
  by_cases hf : fittingSubgroup C ≤ center C
  · have hr : solvableRadical C = center C := by
      apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
      exact le_solvableRadical (center C) inferInstance
        (Group.isSolvable_of_comm (fun a b => Subtype.ext
          (mem_center_iff.mp a.property b).symm))
    let := hC.perfect
    let := hC.isSimpleGroup_quotient_solvableRadical
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
  obtain ⟨hs,_⟩ := ChapterA.Section03.NoncentralFitting.structure_of_noncentral hsq hO hC hf
  rcases hs with hn | hn
  · obtain ⟨p,hp,hl,F,_,_,hF,v,e,_⟩ := hn.2
    have hc : Nat.card C = p^2 * (p * (p^2-1)) := by
      rw [← (generalizedFitting C).card_mul_index,index_eq_card,
        Nat.card_congr v.toEquiv,Nat.card_congr e.toEquiv,
        GorensteinWalter.sl2_card_formula,hF]
      change Nat.card (Fin 2 → F) * _ = _
      rw [Nat.card_fun,Nat.card_fin,hF]
    have hp3 : p^3 ∣ Nat.card C := by
      rw [hc,←mul_assoc,←pow_succ]
      exact dvd_mul_right _ _
    exact (no_natural_order hp hl (hp3.trans hd)).elim
  · obtain ⟨p,hp,ho,hnc⟩ := ChapterA.Section03.NoncentralFitting.exists_noncentral_odd_core hC hO hf
    have hne : pCore p C ≠ ⊥ := fun he => hnc (he ▸ bot_le)
    let : Fact p.Prime := ⟨hp⟩
    have hpd : p ∣ Nat.card (pCore p C) :=
      (pCore_isPGroup (p := p) (G := C)).card_eq_or_dvd.resolve_left
        (fun he => hne ((pCore p C).eq_bot_iff_card.mpr he))
    have hpf : p ∣ Nat.card (generalizedFitting C) := by
      rw [hn.1]
      exact hpd.trans (card_dvd_of_le (pCore_le_fitting C p))
    obtain ⟨hcon,hshape⟩ := hn.2.2.2 p hp hpf
    have hl : 3 < p := by
      have ht := hp.two_le
      rcases hcon with (hcon | hcon) | hcon <;> omega
    have hsquare : p^2 ∣ Nat.card (pCore p C) := by
      rcases hshape with ⟨⟨_,hc⟩,_⟩ | ⟨a,ha,⟨e⟩⟩
      · rw [hc]; exact pow_dvd_pow p (by decide : 2 ≤ 1+2*1)
      · rw [Nat.card_congr e.toEquiv]
        change p^2 ∣ Nat.card (Fin 2 → ZMod (p^a))
        rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod,←pow_mul]
        exact pow_dvd_pow p (by omega)
    have hsquareF : p^2 ∣ Nat.card (generalizedFitting C) := by
      rw [hn.1]
      exact hsquare.trans (card_dvd_of_le (pCore_le_fitting C p))
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hn.2.2.1
    have hc : Nat.card C = Nat.card (generalizedFitting C) * 120 := by
      rw [← (generalizedFitting C).card_mul_index,index_eq_card,
        Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,hF]
      norm_num
    have hdiv : p^2 * 120 ∣ Nat.card C := by
      rw [hc]
      exact Nat.mul_dvd_mul_right hsquareF 120
    exact (no_nilpotent_order hp hl (hdiv.trans hd)).elim

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

private theorem point_quotient_quasisimple_of_order
    (h : EarlierGeometry E)
    (hd : Nat.card (E.Kz ⧸ pCore 2 E.Kz) ∣ sporadicOrderBound) :
    IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz) := by
  let Q := E.Kz ⧸ pCore 2 E.Kz
  have hlocal := E.input.source.simpleQTKE.twoLocal_sqtk
    (point_twoLocal E h.point_mem h.point_fixed h.point_ne_one)
  have hs : IsSQTK KnownSimple.IsKnownSimple E.Kz :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.point_component.1)).mp
      (hlocal.subgroup (E.Kz.subgroupOf (Gz E)))
  have hQ := ChapterE.Structure.sqtk_two_quotient hs (pCore 2 E.Kz) pCore_isPGroup
  have htop : (⊤ : Subgroup E.Kz).IsCComponent := by
    simpa only [subgroupOf_self] using
      h.point_component.2.subgroupOf_of_le le_rfl h.point_component.1
  let : Group.IsNilpotent (pCore 2 E.Kz) := pCore_isNilpotent
  have hbar : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop.map_quotient (pCore 2 E.Kz)
  have hd' : Nat.card (⊤ : Subgroup Q) ∣ sporadicOrderBound := by
    rw [Nat.card_congr (topEquiv (G := Q)).toEquiv]
    exact hd
  exact (quasisimple_of_sporadic_order hQ (pCore_quotient_pCore_eq_bot 2) hbar hd').of_mulEquiv topEquiv

private theorem small_sporadic_card {A : Type*} [Group A] [Finite A]
    (hm : Nonempty (A ≃* Janko1.Model) ∨
      Nonempty (A ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (A ≃* Sporadic.Mathieu.M22) ∨ IsM22Cover A ∨
      Nonempty (A ≃* Sporadic.Mathieu.M23)) : Nat.card A ∣ sporadicOrderBound := by
  rcases hm with e | e | e | hm | e
  · rw [Nat.card_congr e.some.toEquiv,Janko1.card_model]
    norm_num [sporadicOrderBound]
  · rw [Nat.card_congr e.some.toEquiv,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    norm_num [sporadicOrderBound]
  · rw [Nat.card_congr e.some.toEquiv,Sporadic.Mathieu.m22_order]
    norm_num [sporadicOrderBound]
  · have hc : Nat.card (center A) = 3 := by
      rw [Nat.card_congr hm.2.1.some.toEquiv]
      change Nat.card (ZMod 3) = 3
      exact Nat.card_zmod 3
    rw [←(center A).card_mul_index,index_eq_card,hc,
      Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order]
    norm_num [sporadicOrderBound]
  · rw [Nat.card_congr e.some.toEquiv,Sporadic.Mathieu.m23_order]
    norm_num [sporadicOrderBound]

/-- In each of the J₁, J₂, M₂₂, triple M₂₂ and M₂₃ containing rows,
the original point quotient is quasisimple. The two nonquasisimple
A.3.6 alternatives are excluded using the literal quotient order, with
no splitting or bound on the homocyclic exponent assumed. -/
theorem point_quasisimple_in_small_sporadic
    (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J)
    (hm : Nonempty ((J ⧸ pCore 2 J) ≃* Janko1.Model) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M22) ∨
      IsM22Cover (J ⧸ pCore 2 J) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23)) :
    IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz) := by
  obtain ⟨_,C,_,_,_,⟨e⟩,_⟩ := proper_local_model_image h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h)
    hlt (MulEquiv.refl (J ⧸ pCore 2 J))
  apply point_quotient_quasisimple_of_order h
  rw [Nat.card_congr e.toEquiv]
  exact (card_quotient_dvd_card (pCore 2 C)).trans
    (C.card_subgroup_dvd_card.trans (small_sporadic_card hm))

private theorem nonquasisimple_large_primeRank
    {A : Type*} [Group A] [Finite A]
    (hsq : IsSQTK KnownSimple.IsKnownSimple A) (hO : pCore 2 A = ⊥)
    {C : Subgroup A} (hC : C.IsCComponent) (hn : ¬ IsQuasisimple C) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ 2 ≤ primeRank p C := by
  have hf : ¬ fittingSubgroup C ≤ center C := by
    intro hf
    apply hn
    have hr : solvableRadical C = center C := by
      apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
      exact le_solvableRadical (center C) inferInstance
        (Group.isSolvable_of_comm (fun a b => Subtype.ext
          (mem_center_iff.mp a.property b).symm))
    let := hC.perfect
    let := hC.isSimpleGroup_quotient_solvableRadical
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
  obtain ⟨p,hp,ho,hnc⟩ := ChapterA.Section03.NoncentralFitting.exists_noncentral_odd_core hC hO hf
  let : Fact p.Prime := ⟨hp⟩
  have hne : pCore p C ≠ ⊥ := fun he => hnc (he ▸ bot_le)
  have hpd : p ∣ Nat.card (pCore p C) :=
    (pCore_isPGroup (p := p) (G := C)).card_eq_or_dvd.resolve_left
      (fun he => hne ((pCore p C).eq_bot_iff_card.mpr he))
  have hpf : p ∣ Nat.card (fittingSubgroup C) :=
    hpd.trans (card_dvd_of_le (pCore_le_fitting C p))
  obtain ⟨hs,_⟩ := ChapterA.Section03.NoncentralFitting.structure_of_noncentral hsq hO hC hf
  have hl : 3 < p := by
    rcases hs with ⟨he,q,hq,hq3,F,_,_,hF,v,_⟩ | hs
    · rw [←he,Nat.card_congr v.toEquiv] at hpf
      change p ∣ Nat.card (Fin 2 → F) at hpf
      rw [Nat.card_fun,Nat.card_fin,hF] at hpf
      exact (Nat.prime_eq_prime_of_dvd_pow hp hq hpf).symm ▸ hq3
    · have hpf' : p ∣ Nat.card (generalizedFitting C) := hs.1.symm ▸ hpf
      have hc := (hs.2.2.2 p hp hpf').1
      have ht := hp.two_le
      rcases hc with (hc | hc) | hc <;> omega
  refine ⟨p,hp,hl,?_⟩
  by_contra! hr
  have hrc : primeRank p (pCore p C) ≤ 1 :=
    (_root_.primeRank_le_of_injective p (pCore p C).subtype (pCore p C).subtype_injective).trans (by omega)
  let : IsCyclic (pCore p C) := pCore_isPGroup.isCyclic_of_odd_of_elementary_card_le ho
    (fun B hB => by
      let : IsElementaryAbelian p B := hB
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hrc B)
  let := hC.perfect
  have hc : (⊤ : Subgroup C) ≤ centralizer (pCore p C : Set C) := by
    simpa only [Group.IsPerfect.commutator_eq_top] using
      commutator_le_centralizer_of_isCyclic_normal (pCore p C)
  apply hnc
  intro x hx
  exact mem_center_iff.mpr (fun y => (hc (mem_top y) x hx).symm)

/-- A nonquasisimple original point quotient has rank at least two at
some prime greater than three. The prime is constructed from the actual
noncentral Fitting core and the full A.3.6 alternatives. -/
theorem point_nonquasisimple_large_primeRank (h : EarlierGeometry E)
    (hn : ¬ IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ 2 ≤ primeRank p (E.Kz ⧸ pCore 2 E.Kz) := by
  let Q := E.Kz ⧸ pCore 2 E.Kz
  have hlocal := E.input.source.simpleQTKE.twoLocal_sqtk
    (point_twoLocal E h.point_mem h.point_fixed h.point_ne_one)
  have hs : IsSQTK KnownSimple.IsKnownSimple E.Kz :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.point_component.1)).mp
      (hlocal.subgroup (E.Kz.subgroupOf (Gz E)))
  have hQ := ChapterE.Structure.sqtk_two_quotient hs (pCore 2 E.Kz) pCore_isPGroup
  have htop : (⊤ : Subgroup E.Kz).IsCComponent := by
    simpa only [subgroupOf_self] using
      h.point_component.2.subgroupOf_of_le le_rfl h.point_component.1
  let : Group.IsNilpotent (pCore 2 E.Kz) := pCore_isNilpotent
  have hbar : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop.map_quotient (pCore 2 E.Kz)
  obtain ⟨p,hp,hl,hr⟩ := nonquasisimple_large_primeRank hQ
    (pCore_quotient_pCore_eq_bot 2) hbar (fun hqs => hn (hqs.of_mulEquiv topEquiv))
  rw [primeRank_equiv p (topEquiv (G := Q))] at hr
  exact ⟨p,hp,hl,hr⟩

private theorem point_quasisimple_of_large_rank_bound
    (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J)
    {A : Type*} [Group A] [Finite A] (e : (J ⧸ pCore 2 J) ≃* A)
    (hb : ∀ (S : Sylow 2 A) (C : Subgroup A), (S : Subgroup A) ≤ C → C ≠ ⊤ →
      ∀ p : ℕ, p.Prime → 3 < p → primeRank p C ≤ 1) :
    IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz) := by
  by_contra hn
  obtain ⟨p,hp,hl,hr⟩ := point_nonquasisimple_large_primeRank h hn
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨P,C,hC,hproper,_,⟨b⟩,htop⟩ := proper_local_model_image h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt e
  have hc : C ⊔ (P : Subgroup A) ≠ ⊤ :=
    ChapterA.Section03.SourceEmbeddings.local_sup_ne_top_of_ne_top htop P C hC hproper
  have hbound := hb P (C ⊔ (P : Subgroup A)) le_sup_right hc p hp hl
  rw [primeRank_equiv p b] at hr
  have hlow := hr.trans ((primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (primeRank_mono p (show C ≤ C ⊔ (P : Subgroup A) from le_sup_left)))
  omega

/-- The literal full-Sylow overgroup bounds in HS and Ru exclude both
nonquasisimple point alternatives, without imposing a reduced proper-pair list. -/
theorem point_quasisimple_in_higmanSims_or_rudvalis
    (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J)
    (hm : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Rudvalis.Model)) :
    IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz) := by
  rcases hm with hm | hm
  · let e := hm.some
    apply point_quasisimple_of_large_rank_bound h hJ hlt e
    intro P C hPC hc p hp hl
    let : Fact p.Prime := ⟨hp⟩
    exact Sporadic.LeechRelated.HS.SylowOvergroups.proper_overgroup_primeRank_le_one
      P C hPC hc hl (hp.odd_of_ne_two (by omega))
  · let e := hm.some
    have hO : pCore 2 Rudvalis.Model = ⊥ := by
      rw [←pCore_map_iso 2 e,pCore_quotient_pCore_eq_bot 2,Subgroup.map_bot]
    apply point_quasisimple_of_large_rank_bound h hJ hlt e
    intro P C hPC hc p hp hl
    let : Fact p.Prime := ⟨hp⟩
    exact ChapterA.Section03.SourceEmbeddings.rudvalis_proper_overgroup_primeRank_le_one
      hO P C hPC hc hl


/-- The seven sporadic containing rows give field four and a quasisimple
point quotient on the original chosen flag. The complete containing
catalogue supplies the field parameter; the order and full-Sylow rank
arguments supply quasisimplicity. The J₄ row is retained separately. -/
theorem ofFlag_sporadic_point_comparison
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    (hm : Nonempty ((J ⧸ pCore 2 J) ≃* Janko1.Model) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M22) ∨
      IsM22Cover (J ⧸ pCore 2 J) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Rudvalis.Model)) :
    S.field.degree = 2 ∧
      IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) := by
  refine ⟨(ofFlag_proper_overcomponent_fieldFour S f X z H h hne hlinear h1132 e hJ hlt).1,?_⟩
  rcases hm with h1 | h2 | h22 | hcover | h23 | hhs | hru
  · exact point_quasisimple_in_small_sporadic h hJ hlt (.inl h1)
  · exact point_quasisimple_in_small_sporadic h hJ hlt (.inr (.inl h2))
  · exact point_quasisimple_in_small_sporadic h hJ hlt (.inr (.inr (.inl h22)))
  · exact point_quasisimple_in_small_sporadic h hJ hlt (.inr (.inr (.inr (.inl hcover))))
  · exact point_quasisimple_in_small_sporadic h hJ hlt (.inr (.inr (.inr (.inr h23))))
  · exact point_quasisimple_in_higmanSims_or_rudvalis h hJ hlt (.inl hhs)
  · exact point_quasisimple_in_higmanSims_or_rudvalis h hJ hlt (.inr hru)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
