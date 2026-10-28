module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.SourceStructure.Centralizer
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The linked SL₂ quotient and residual normalizer section

The A.3.6 alternatives give an actual equivalence of L/O₂,F(L) with SL₂(r),
where r = p in the natural case and r = 5 in the nilpotent case. Transport
through the local quotient equivalence preserves the full Fitting subgroup.

The Frattini factorization gives L = C_L(X/O₂(X))Y. The first factor is
solvable and normal, so its image in the quasisimple Fitting quotient is
central. A subgroup supplementing the center of a perfect group is the
whole group; consequently Y surjects onto this same SL₂(r) quotient.

Assuming X ≤ Y, a second Frattini argument gives Y = X N_Y(P). The actual
image of X lies in Ω₁(O_p(L/O₂(L))) ≤ F(L/O₂(L)), even when the p-core has
higher homocyclic exponent. Thus N_Y(P) still surjects. Its kernel and the
first isomorphism theorem construct the required section, with the same r.

The earlier source implications and the original N_L(P)-irreducibility
witness are explicit inputs. The containment X ≤ Y is discharged by the
residual-actions owner in the parent assembly.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed p.512, using A.3.6, pp.43–45.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.ChapterA.Section04

namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
universe u

private theorem fitting_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

private theorem fitting_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom = fittingSubgroup B := by
  apply le_antisymm (fitting_map_le e)
  have h := map_mono (f := e.toMonoidHom) (fitting_map_le e.symm)
  simpa [map_map] using h

private theorem source_model {A E : Type*} [Group A] [Finite A] [Group E] [Finite E]
    {C : Subgroup E} (e : A ≃* C) (h : A36Conclusion C)
    (hn : ¬ IsQuasisimple A) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup A)) :
    IsQuasisimple (A ⧸ fittingSubgroup A) ∧
      ∃ r : ℕ, r.Prime ∧ (r = p ∨ r = 5) ∧ IsSL (A ⧸ fittingSubgroup A) 2 r := by
  let eF : fittingSubgroup A ≃* fittingSubgroup C :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (fitting_map e))
  let eQ := QuotientGroup.congr _ _ e (fitting_map e)
  have hnC : ¬ IsQuasisimple C := by
    intro hc
    let := hc
    exact hn (IsQuasisimple.of_mulEquiv e.symm)
  have hdC : p ∣ Nat.card (fittingSubgroup C) := by
    rwa [← Nat.card_congr eF.toEquiv]
  refine ⟨?_, ?_⟩
  · let := h.2.2.1
    exact IsQuasisimple.of_mulEquiv eQ.symm
  · rcases RadicalStructure.nonsimple_radical h hnC with hnat | hnil
    · obtain ⟨hF, r, hr, hr3, ha⟩ := hnat
      obtain ⟨_, hc⟩ := RadicalStructure.natural_elementary ha
      have hd' : p ∣ r ^ 2 := by simpa only [← hF, hc] using hdC
      have hpr : p = r := (Nat.prime_dvd_prime_iff_eq Fact.out hr).mp
        ((Fact.out : p.Prime).dvd_of_dvd_pow hd')
      subst r
      obtain ⟨F, hfield, hfin, hcard, v, ρ, hact⟩ := ha
      exact ⟨p, Fact.out, Or.inl rfl, F, hfield, hfin, hcard,
        ⟨eQ.trans ((QuotientGroup.quotientMulEquivOfEq hF.symm).trans ρ)⟩⟩
    · obtain ⟨F, hfield, hfin, hcard, ⟨eS⟩⟩ := hnil.2.2.1
      exact ⟨5, by decide, Or.inr rfl, F, hfield, hfin, hcard,
        ⟨eQ.trans ((QuotientGroup.quotientMulEquivOfEq hnil.1.symm).trans eS)⟩⟩

private theorem central_supplement_eq_top {Q : Type*} [Group Q] [Group.IsPerfect Q]
    (B : Subgroup Q) (hB : center Q ⊔ B = ⊤) : B = ⊤ := by
  have hnormalizer : (⊤ : Subgroup Q) ≤ normalizer (B : Set Q) := by
    rw [← hB]
    exact sup_le (Subgroup.center_le_normalizer (B : Set Q)) B.le_normalizer
  let : B.Normal := normalizer_eq_top_iff.mp (top_unique hnormalizer)
  apply top_unique
  simpa only [Group.IsPerfect.commutator_eq_top] using
    (Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      (sup_comm B (center Q) |>.trans hB) (inferInstance : IsMulCommutative (center Q)))

private theorem solvable_normal_central {A Q : Type*} [Group A] [Group Q]
    [IsQuasisimple Q] (C : Subgroup A) [C.Normal] [Group.IsSolvable C]
    (f : A →* Q) (hf : Function.Surjective f) : C.map f ≤ center Q := by
  let : (C.map f).Normal := (inferInstance : C.Normal).map f hf
  let : Group.IsSolvable (C.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective C)
  rcases IsQuasisimple.normal_le_center_or_eq_top (C.map f) with hc | ht
  · exact hc
  · have hs : Group.IsSolvable Q := Group.isSolvable_of_surjective
      (f := (C.map f).subtype) (by rw [ht]; exact topEquiv.surjective)
    let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
    let : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
    exact (Group.IsPerfect.not_isSolvable Q hs).elim

private theorem residual_surjects {G Q : Type*} [Group G] [Finite G] [Group Q]
    [IsQuasisimple Q] (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T) (hT : T ≤ normalizer (L : Set G))
    (hsol : Group.IsSolvable (twoSectionCentralizer (XiP p L) (L ⊔ T)))
    (f : L →* Q) (hf : Function.Surjective f) :
    ((normalizerResidual L (radicalCore p L T)).subgroupOf L).map f = ⊤ := by
  let C := twoSectionCentralizer (XiP p L) (L ⊔ T)
  let Y := normalizerResidual L (radicalCore p L T)
  let : Group.IsSolvable C := hsol
  let : Group.IsSolvable (C.subgroupOf L) := Group.isSolvable_of_isSolvable_injective
    (f := L.subtype.subgroupComap C) (by
      intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : C => (x : G)) hab)))
  let : (C.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer
    (le_sup_left.trans (twoSectionCentralizer_normalized _ _
      ((sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L))))
  have hc := solvable_normal_central (C.subgroupOf L) f hf
  have hcover : C.subgroupOf L ⊔ Y.subgroupOf L = ⊤ := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_comm C L,
      map_subgroupOf_eq_of_le (normalizerResidual_le _ _),
      ← MonoidHom.range_eq_map, range_subtype]
    exact le_antisymm (sup_le inf_le_left (normalizerResidual_le _ _))
      (L_covered_by_Y_inside p L T hL hT)
  apply central_supplement_eq_top
  apply top_unique
  rw [← map_top_of_surjective f hf, ← hcover, Subgroup.map_sup]
  exact sup_le_sup_right hc _

private theorem sylow_normalizer_surjects {G Q : Type*} [Group G] [Finite G] [Group Q]
    {p : ℕ} [Fact p.Prime] (X Y L : Subgroup G)
    (hXY : X ≤ Y) (hYL : Y ≤ L) (hYX : Y ≤ normalizer (X : Set G))
    (f : L →* Q) (hY : (Y.subgroupOf L).map f = ⊤)
    (hX : X.subgroupOf L ≤ f.ker) (P : Sylow p X) :
    ((Y ⊓ normalizer ((P : Subgroup X).map X.subtype : Set G)).subgroupOf L).map f = ⊤ := by
  let P₀ := (P : Subgroup X).map X.subtype
  let N := Y ⊓ normalizer (P₀ : Set G)
  have hgen : N ⊔ X = Y := by
    apply le_antisymm (sup_le inf_le_left hXY)
    let X' := X.subgroupOf Y
    let : X'.Normal := normal_subgroupOf_of_le_normalizer hYX
    let e := (subgroupOfEquivOfLe hXY).symm
    let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
    have hh := congrArg (map Y.subtype) P'.normalizer_sup_eq_top
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
      map_subgroupOf_eq_of_le hXY] at hh
    apply hh.symm.le.trans (sup_le _ le_sup_right)
    apply le_trans _ le_sup_left
    apply le_inf (map_subtype_le _)
    have hm := ((P' : Subgroup X').map X'.subtype).le_normalizer_map Y.subtype
    have hmap : (((P' : Subgroup X').map X'.subtype).map Y.subtype) = P₀ := by
      change (((P : Subgroup X).map e.toMonoidHom).map X'.subtype).map Y.subtype = P₀
      rw [map_map, map_map]
      rfl
    rwa [hmap] at hm
  have hg : N.subgroupOf L ⊔ X.subgroupOf L = Y.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (inf_le_left.trans hYL),
      map_subgroupOf_eq_of_le (hXY.trans hYL), map_subgroupOf_eq_of_le hYL]
    exact hgen
  have hm := congrArg (map f) hg
  have hb : (X.subgroupOf L).map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hX
  rw [Subgroup.map_sup, hb, sup_bot_eq, hY] at hm
  exact hm

private theorem radical_in_fitting_kernel {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) :
    (XiP p L).subgroupOf L ≤
      ((QuotientGroup.mk' (fittingSubgroup (XiQuotient L))).comp
        (QuotientGroup.mk' (pCore 2 L))).ker := by
  rw [XiP_subgroupOf]
  intro x hx
  have hp : x ∈ xiPPreimage p L := map_subtype_le _ hx
  apply (QuotientGroup.eq_one_iff _).mpr
  exact pCore_le_fitting (XiQuotient L) p (map_subtype_le _ hp)

private theorem section_from_surjection {G Q : Type*} [Group G] [Group Q]
    (N L : Subgroup G) (hNL : N ≤ L) (f : L →* Q)
    (hs : (N.subgroupOf L).map f = ⊤) {r : ℕ} (hQ : IsSL Q 2 r) :
    ∃ S : Subgroup G, S ≤ N ∧ ∃ K : Subgroup S, ∃ _ : K.Normal, IsSL (S ⧸ K) 2 r := by
  let g := f.comp (inclusion hNL)
  have hg : Function.Surjective g := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, inclusion_range]
    exact hs
  obtain ⟨F, hfield, hfin, hcard, ⟨e⟩⟩ := hQ
  exact ⟨N, le_rfl, g.ker, inferInstance, F, hfield, hfin, hcard,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective g hg).trans e⟩⟩

/-- A.3.6 supplies the actual Fitting quotient, with the natural-case prime
identified with the given Fitting prime p. Higher homocyclic exponents in
the nilpotent alternative are unrestricted. -/
theorem fittingQuotient_SL_of_source
    {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    {T L : Subgroup G} (hL : L ∈ CFSG.Quasithin.Chapter1.L G T)
    (hQ : IsSQTK 𝒦 ((L ⊔ T : Subgroup G) ⧸ pCore 2 (L ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    IsQuasisimple (XiQuotient L ⧸ fittingSubgroup (XiQuotient L)) ∧
      ∃ r : ℕ, r.Prime ∧ (r = p ∨ r = 5) ∧
        IsSL (XiQuotient L ⧸ fittingSubgroup (XiQuotient L)) 2 r :=
  source_model (radicalLocalQuotientEquiv hL)
    (proposition_1_2_1_four_earlier_conclusion hA36 hQ hL.1) hn hd

/-- The same prime r occurs in L/O₂,F(L) and the actual SL₂(r) section of
N_Y(P). The section is constructed using the kernel of a surjective map.
Only the containment X ≤ Y is an additional residual input; the centralizer
solvability needed in the argument is proved from the earlier source inputs. -/
theorem residual_SL_section_of_source
    {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T L : Subgroup G} (hL : L ∈ LStar G T)
    (hQ : IsSQTK 𝒦 ((L ⊔ T : Subgroup G) ⧸ pCore 2 (L ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (P : Sylow p (XiP p L))
    (hirr : ∀ A : Subgroup
        (((P : Subgroup (XiP p L)).map (XiP p L).subtype) ⧸
          frattini ((P : Subgroup (XiP p L)).map (XiP p L).subtype)),
      (∀ g : (L ⊓ normalizer
          ((P : Subgroup (XiP p L)).map (XiP p L).subtype : Set G) : Subgroup G),
        ∀ a ∈ A, frattiniConjugationAction _ _ inf_le_right g a ∈ A) →
        A = ⊥ ∨ A = ⊤)
    (hXY : XiP p L ≤ normalizerResidual L (radicalCore p L T)) :
    ∃ r : ℕ, r.Prime ∧ (r = p ∨ r = 5) ∧
      IsSL (XiQuotient L ⧸ fittingSubgroup (XiQuotient L)) 2 r ∧
      ∃ S : Subgroup G,
        S ≤ normalizerResidual L (radicalCore p L T) ⊓
          normalizer ((P : Subgroup (XiP p L)).map (XiP p L).subtype : Set G) ∧
        ∃ K : Subgroup S, ∃ _ : K.Normal, IsSL (S ⧸ K) 2 r := by
  have hT := radicalLocal_invariant_of_A38 hA38 hL.1 hQ hn
  have hsol := sectionCentralizer_solvable_of_source hA36 hA38 hL hQ hn ho hd P hirr
  obtain ⟨hqs, r, hr, hrp, hmodel⟩ := fittingQuotient_SL_of_source hA36 hL.1 hQ hn hd
  let := hqs
  let f := (QuotientGroup.mk' (fittingSubgroup (XiQuotient L))).comp
    (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hY := residual_surjects p L T hL.1 hT hsol f hf
  have hN := sylow_normalizer_surjects (XiP p L) _ L hXY
    (normalizerResidual_le _ _)
    ((normalizerResidual_le _ _).trans (XiP_invariant p L.le_normalizer))
    f hY (radical_in_fitting_kernel p L) P
  exact ⟨r, hr, hrp, hmodel,
    section_from_surjection _ L (inf_le_left.trans (normalizerResidual_le _ _)) f hN hmodel⟩

end CFSG.Quasithin.Chapter1.RadicalNormalizers
