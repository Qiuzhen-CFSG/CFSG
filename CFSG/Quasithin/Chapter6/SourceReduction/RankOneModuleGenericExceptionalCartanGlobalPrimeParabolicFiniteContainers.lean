module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicCommonSieve
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.Mathieu.M24.Properties.Order

/-!
# Finite common containers of the original diagram residual

The intrinsic two-core quotient of the original residual has order dividing
its literal image in the common component modulo the ambient two-core.
This follows by transporting through the actual two-group kernel; the cubic
scalar center in the special-linear case is retained.

For the alternating, binary higher-linear and sporadic carriers with known
orders, the defining two-part bounds the residual field degree. The exact
orders then force degree two. The original exclusion of PSL₃(4) leaves only
the full SL₃(4) quotient, of order 60480. Its order excludes A₈, PSL₄(2),
PSL₅(2), M₁₁, M₁₂, M₂₂, M₂₃ and HS. The surviving M₂₄, J₂, J₄, Rudvalis
and cubic M₂₂ rows consequently have original SL₃(4) residual and selected
PSL₂(4) parabolic. Held, rank-two and binary ternary rows remain explicit.

The final theorem applies the reduction to the same source pair, preserving
relative normality, strict changed orbit, full Sylows and both original
Cartans. It does not assume that the selected parabolic is an H-component.

Source: Aschbacher–Smith A.3.12 and 5.2.2, printed pp.47–48,648–649,
refs/quasithin.pdf. The concrete orders are the proved native carrier orders
in the imported modules; the matrix orders follow from their flag counts.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels

private def finiteOrders : Finset ℕ :=
  {20160,9999360,7920,95040,443520,10200960,244823040,604800,
    86775571046077562880,44352000,145926144000,1330560}

private theorem finite_order_degree {f C : ℕ} (hf : 1 < f)
    (hC : C ∈ finiteOrders) (hpart : 2^(3*f) ∣ C)
    (hd : ((2^f)^3*((2^f)^3-1)*((2^f)^2-1)) / Nat.gcd 3 (2^f-1) ∣ C ∨
      (2^f)^3*((2^f)^3-1)*((2^f)^2-1) ∣ C ∨
      (2^f)^4*((2^f)^2-1)*((2^f)^4-1) ∣ C) : f = 2 := by
  have hn : ¬ 2^24 ∣ C := by
    simp only [finiteOrders,Finset.mem_insert,Finset.mem_singleton] at hC
    rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hf7 : f ≤ 7 := by
    by_contra! hgt
    exact hn ((pow_dvd_pow 2 (by omega : 24 ≤ 3*f)).trans hpart)
  by_contra hne
  have hf3 : 3 ≤ f := by omega
  simp only [finiteOrders,Finset.mem_insert,Finset.mem_singleton] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases f <;> norm_num at hd

private theorem diagram_finite_order
    {Q : Type*} [Group Q] [Finite Q] {f C : ℕ} (hf : 1 < f)
    (hC : C ∈ finiteOrders) (hd : Nat.card Q ∣ C)
    (hm : ClassicalGroup.IsPSL Q 3 (2^f) ∨ IsSL Q 3 (2^f) ∨
      ClassicalGroup.IsPSp Q 2 (2^f)) : f = 2 := by
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · have hp := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.card_unipotent F,hF,←pow_mul,Nat.mul_comm f 3,←Nat.card_congr e.toEquiv] at hp
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF] at hd
    exact finite_order_degree hf hC (hp.trans (by
      simpa only [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF] using hd)) (.inl hd)
  · rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF] at hd
    have hp : 2^(3*f) ∣ C := by
      rw [Nat.mul_comm 3 f,pow_mul]
      exact (dvd_mul_of_dvd_left (dvd_mul_right _ _) _).trans hd
    exact finite_order_degree hf hC hp (.inr (.inl hd))
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
    rw [Nat.card_congr a.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hd
    have hp : 2^(3*f) ∣ C := by
      apply (pow_dvd_pow 2 (by omega : 3*f ≤ 4*f)).trans
      rw [Nat.mul_comm 4 f,pow_mul]
      exact (dvd_mul_of_dvd_left (dvd_mul_right _ _) _).trans hd
    exact finite_order_degree hf hC hp (.inr (.inr hd))

variable {G : Type*} [Group G] [Finite G]

/-- The intrinsic two-core quotient of the original residual has order
 dividing its literal containing image, retaining the central cubic kernel. -/
theorem original_residual_card_dvd_common_image
    {H X I : Subgroup G} (hIX : I ≤ X) (hKI : residual H ≤ I) :
    Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∣
      Nat.card ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) := by
  let K := residual H
  have hKX : K ≤ X := hKI.trans hIX
  let q := QuotientGroup.mk' (pCore 2 X)
  let Kbar := (K.subgroupOf X).map q
  let r := q.subgroupMap (K.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a : pResidual 2 H ≃* K :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let b := a.trans (subgroupOfEquivOfLe hKX).symm
  let c := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
    (r.quotientPCoreEquivOfSurjective (q.subgroupMap_surjective _) hr)
  rw [Nat.card_congr c.toEquiv]
  exact (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 Kbar))
    (QuotientGroup.mk'_surjective _)).trans (card_dvd_of_le (map_mono (comap_mono hKI)))

private theorem SelectedSourceModels.parabolic_common_finite_order
    {H R X I : Subgroup G} (hs : SelectedSourceModels H R)
    (hn : ¬ (R.subgroupOf H).IsCComponent)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hIX : I ≤ X) (hKI : residual H ≤ I)
    (hc : Nat.card ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) ∈ finiteOrders) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
      IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 ∧
      60480 ∣ Nat.card ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) := by
  obtain ⟨f,hf,hR,hm⟩ := hs.resolve_left hn
  have hd := original_residual_card_dvd_common_image hIX hKI
  have he := diagram_finite_order hf hc hd hm
  subst f
  have hSL : IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 := by
    rcases hm with hm | hm | ⟨F,_,_,hF,⟨e⟩⟩
    · exact (hthree hm).elim
    · exact hm
    · let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
        (by simpa only [Nat.card_eq_fintype_card] using hF)
      let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
      rw [Nat.card_congr a.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hd
      simp only [finiteOrders,Finset.mem_insert,Finset.mem_singleton] at hc
      rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;>
        rw [hc] at hd <;> norm_num at hd
  refine ⟨hR,hSL,?_⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hSL
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF] at hd
  norm_num at hd ⊢
  exact hd

private theorem binary_linear_card {Y : Type*} [Group Y]
    {m : ℕ} (hm : m = 4 ∨ m = 5) (h : ClassicalGroup.IsPSL Y m 2) :
    Nat.card Y = 20160 ∨ Nat.card Y = 9999360 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let : NeZero m := ⟨by rcases hm with rfl | rfl <;> decide⟩
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) m
  rw [hF,←Nat.card_congr e.toEquiv] at hc
  rcases hm with rfl | rfl
  · left; norm_num [Fin.prod_univ_succ] at hc; exact hc
  · right; norm_num [Fin.prod_univ_succ] at hc; exact hc

private theorem sporadic_finite_order
    (name : ClassificationModels.SporadicName) (hn : name ≠ .j3) (hh : name ≠ .he) :
    Nat.card name.Carrier ∈ finiteOrders := by
  cases name <;> try contradiction
  all_goals
    simp only [ClassificationModels.SporadicName.Carrier]
    first
    | rw [Sporadic.Mathieu.m11_order]
    | rw [Sporadic.Mathieu.m12_order]
    | rw [Sporadic.Mathieu.m22_order]
    | rw [Sporadic.Mathieu.m23_order]
    | rw [Sporadic.Mathieu.m24_order]
    | rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    | rw [Janko4.Cardinality.model_card]
    | rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
    | rw [Rudvalis.model_card]
    norm_num [finiteOrders]

private theorem sporadic_of_cubic_order
    (name : ClassificationModels.SporadicName) (hn : name ≠ .j3) (hh : name ≠ .he)
    (hd : 60480 ∣ Nat.card name.Carrier) :
    name = .m24 ∨ name = .j2 ∨ name = .j4 ∨ name = .ru := by
  cases name <;> try contradiction
  all_goals try solve | simp
  all_goals
    simp only [ClassificationModels.SporadicName.Carrier] at hd
    first
    | rw [Sporadic.Mathieu.m11_order] at hd
    | rw [Sporadic.Mathieu.m12_order] at hd
    | rw [Sporadic.Mathieu.m22_order] at hd
    | rw [Sporadic.Mathieu.m23_order] at hd
    | rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at hd
    norm_num at hd

private theorem mathieu_cover_card {Y : Type*} [Group Y] [Finite Y]
    (hm : IsM22Cover Y) : Nat.card Y = 1330560 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center Y),
    Nat.card_congr hm.2.2.some.toEquiv,Nat.card_congr hm.2.1.some.toEquiv,
    Sporadic.Mathieu.m22_order]
  norm_num

/-- The original non-PSL₃(4) residual excludes A₈, binary PSL₄/PSL₅,
M₁₁, M₁₂, M₂₂, M₂₃ and HS. The remaining finite rows other than Held,
including the cubic M₂₂ cover, force the full SL₃(4) residual quotient. -/
theorem SelectedSourceModels.parabolic_common_finite_models
    {H R X I : Subgroup G} (hs : SelectedSourceModels H R)
    (hn : ¬ (R.subgroupOf H).IsCComponent)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hIX : I ≤ X) (hKI : residual H ≤ I)
    (hm : let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
      (IsSimpleGroup Ibar ∧
        (IsAlternating Ibar 8 ∨ RankTwoTheoremC Ibar ∨
          (∃ m : ℕ, (m = 4 ∨ m = 5) ∧ ClassicalGroup.IsPSL Ibar m 2) ∨
          ∃ name : ClassificationModels.SporadicName,
            name ≠ .j3 ∧ Nonempty (Ibar ≃* name.Carrier))) ∨
        (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
          ((∃ (unitary : Bool) (f : ℕ), 1 ≤ f ∧
            (2^f) % 3 = (if unitary then 2 else 1) ∧ IsSLSign Ibar unitary 3 (2^f)) ∨
            IsM22Cover Ibar))) :
    let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    (IsSimpleGroup Ibar ∧
      (RankTwoTheoremC Ibar ∨ Nonempty (Ibar ≃* Held.He) ∨
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
          IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 ∧
          ∃ name : ClassificationModels.SporadicName,
            (name = .m24 ∨ name = .j2 ∨ name = .j4 ∨ name = .ru) ∧
            Nonempty (Ibar ≃* name.Carrier)))) ∨
      (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
        ((∃ (unitary : Bool) (f : ℕ), 1 ≤ f ∧
          (2^f) % 3 = (if unitary then 2 else 1) ∧ IsSLSign Ibar unitary 3 (2^f)) ∨
          (IsM22Cover Ibar ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
            IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4))) := by
  let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  have hfinite := hs.parabolic_common_finite_order hn hthree hIX hKI
  rcases hm with ⟨hsimple,hm⟩ | ⟨hc,hm⟩
  · left
    refine ⟨hsimple,?_⟩
    rcases hm with ha | hrank | ⟨m,hm,he⟩ | ⟨name,hname,⟨e⟩⟩
    · obtain ⟨e⟩ := ha
      have hc : Nat.card Ibar = 20160 := by
        rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      have hd := (hfinite (by rw [hc]; norm_num [finiteOrders])).2.2
      rw [hc] at hd
      norm_num at hd
    · exact .inl hrank
    · rcases binary_linear_card hm he with hc | hc
      all_goals
        have hd := (hfinite (by rw [hc]; norm_num [finiteOrders])).2.2
        rw [hc] at hd
        norm_num at hd
    · by_cases hh : name = .he
      · subst name
        exact .inr (.inl ⟨e⟩)
      · obtain ⟨hfour,hSL,hd⟩ := hfinite (by
          rw [Nat.card_congr e.toEquiv]
          exact sporadic_finite_order name hname hh)
        rw [Nat.card_congr e.toEquiv] at hd
        exact .inr (.inr ⟨hfour,hSL,name,sporadic_of_cubic_order name hname hh hd,⟨e⟩⟩)
  · right
    refine ⟨hc,?_⟩
    rcases hm with hm | hm
    · exact .inl hm
    · obtain ⟨hfour,hSL,_⟩ := hfinite (by rw [mathieu_cover_card hm]; norm_num [finiteOrders])
      exact .inr ⟨hm,hfour,hSL⟩

/-- On the same original pair, the finite common containers reduce to M₂₄,
J₂, J₄, Held, Rudvalis and the cubic M₂₂ cover. Except for Held, these
remaining finite rows carry the actual SL₃(4) residual and PSL₂(4) parabolic. -/
theorem source_prime_pair_parabolic_finite_containers
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
            ¬ (R.subgroupOf H).IsCComponent ∧
            (∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
              (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))) ∧
            let X := normalizer (normalizingSylow T R : Set G) ⊔ H
            ∃ I : Subgroup G, residual H ≤ I ∧ I ≤ X ∧
              (I.subgroupOf X).IsCComponent ∧ (I.subgroupOf X).Normal ∧
              conjugateSpanBy R (U : Subgroup G) < I ∧
              let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
              IsQuasisimple Ibar ∧
                ((IsSimpleGroup Ibar ∧
                  (RankTwoTheoremC Ibar ∨ Nonempty (Ibar ≃* Held.He) ∨
                    (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
                      IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 ∧
                      ∃ name : ClassificationModels.SporadicName,
                        (name = .m24 ∨ name = .j2 ∨ name = .j4 ∨ name = .ru) ∧
                        Nonempty (Ibar ≃* name.Carrier)))) ∨
                  (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
                    ((∃ (unitary : Bool) (f : ℕ), 1 ≤ f ∧
                      (2^f) % 3 = (if unitary then 2 else 1) ∧ IsSLSign Ibar unitary 3 (2^f)) ∨
                      (IsM22Cover Ibar ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
                        IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)))))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_parabolic_common_sieve h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,hm⟩
  · exact .inl hz
  exact .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,
    hs.parabolic_common_finite_models hn hthree hIX hKI hm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
