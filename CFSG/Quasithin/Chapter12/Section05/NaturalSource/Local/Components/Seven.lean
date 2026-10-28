module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Rigidity
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryContaining
public import Theory.SpecificGroups.SL2.LinearThreeSection
public import Theory.GroupTheory.PerfectNormalizerLift
public import Theory.SpecificGroups.PSL3Two.ProperSubgroups
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape

/-!
# The original nonquasisimple exterior components

At i = 1 or 3, the actual smaller two-core quotient is SL₃(2), of order
168. The A.3.6 nonquasisimple alternatives, mapped through their solvable
kernels, force the natural prime to be seven and exclude the SL₂(5) row.
Thus the literal K/O₂(K) has elementary seven-core of order 49 and quotient
SL₂(7). The smaller residual covers this SL₂ quotient: its projective image
is full, and perfectness lifts through the central kernel.

The original Ξ₇(K) maps onto that seven-core. Hence Ξ₇(K)Lᵢ covers K/O₂(K).
The original Sylow normalizes Lᵢ and contains O₂(K); perfectness of K removes
the remaining two-group quotient, proving the actual embedded product.
At i = 1 this constructs the complete radical alternative in LocalComponents.
At i = 3 natural-action rigidity leaves only equality or this radical row.
PointCore.Nonquasisimple applies the constructed model to the original V.

The quasisimple point sieve and ambient exclusion of the three-space radical
row remain with qt-d-1251-local, as do normalizers and strict-enlargement
escape. Final source assembly belongs to qt-d-1251-source.
Source: Aschbacher--Smith A.3.6, A.3.12 and12.5.3, pp.43--48,817--819.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels

private theorem seven_core_of_nonquasisimple
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hB : Nat.card (B ⧸ pCore 2 B) = 168)
    (f : B →* A) [Group.IsSolvable f.ker]
    (h : Chapter1.Section02.A36Natural A ∨ Chapter1.Section02.A36Nilpotent A) :
    ElementaryModel 7 2 (pCore 7 A) ∧ IsSL (A ⧸ pCore 7 A) 2 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have parameter (N : Subgroup A) [N.Normal] [Group.IsSolvable N]
      {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hm : IsSL (A ⧸ N) 2 p) : p = 7 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let g := e.toMonoidHom.comp ((QuotientGroup.mk' N).comp f)
    let : Group.IsSolvable g.ker := by
      change Group.IsSolvable (e.toMonoidHom.comp ((QuotientGroup.mk' N).comp f)).ker
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ← MonoidHom.comap_ker,
        QuotientGroup.ker_mk']
      exact isSolvable_comap_of_solvable_ker f N
    exact Theory.SL2.prime_eq_seven_of_solvable_kernel hB hp hp3 hF g
  rcases h with h | h
  · obtain ⟨p,hp,hp3,ha⟩ := h.2
    let N := generalizedFitting A
    let : Group.IsNilpotent N := by change Group.IsNilpotent (generalizedFitting A); rw [h.1]; infer_instance
    obtain ⟨F,_,_,hF,v,ρ,hact⟩ := ha
    have he : p = 7 := parameter N hp hp3 ⟨F,inferInstance,inferInstance,hF,⟨ρ⟩⟩
    have hF7 : Nat.card F = 7 := hF.trans he
    have hc : Nat.card N = 7^2 := (Chapter1.RadicalStructure.natural_elementary
      ⟨F,inferInstance,inferInstance,hF7,v,ρ,hact⟩).2
    have hN : N = pCore 7 A := h.1.trans
      (Chapter1.RadicalStructure.fitting_eq_core (by
        rw [←h.1]; exact IsPGroup.of_card hc))
    let : Fintype F := Fintype.ofFinite F
    have hfc : Fintype.card F = Fintype.card (ZMod 7) := by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF7
    let a : F ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hfc
    refine ⟨?_,?_⟩
    · rw [←hN]
      exact ⟨v.trans (AddEquiv.piCongrRight (fun _ : Fin 2 => a.toAddEquiv)).toMultiplicative⟩
    · exact ⟨F,inferInstance,inferInstance,hF7,
        ⟨(QuotientGroup.quotientMulEquivOfEq hN.symm).trans ρ⟩⟩
  · let := h.2.1
    have he := parameter (generalizedFitting A) (by decide : Nat.Prime 5) (by decide) h.2.2.1
    norm_num at he

private theorem seven_quotient_covered
    {A B : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    [Group B] [Finite B] [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hB : Nat.card (B ⧸ pCore 2 B) = 168)
    (f : B →* A) [Group.IsSolvable f.ker]
    (hm : IsSL (A ⧸ pCore 7 A) 2 7) :
    Function.Surjective ((QuotientGroup.mk' (pCore 7 A)).comp f) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let N := pCore 7 A
  let : Group.IsNilpotent N := pCore_isNilpotent
  let g := e.toMonoidHom.comp ((QuotientGroup.mk' N).comp f)
  let : Group.IsSolvable g.ker := by
    change Group.IsSolvable (e.toMonoidHom.comp ((QuotientGroup.mk' N).comp f)).ker
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ←MonoidHom.comap_ker,
      QuotientGroup.ker_mk']
    exact isSolvable_comap_of_solvable_ker f N
  have hp := (Theory.SL2.prime_seven_and_projective_surjective_of_solvable_kernel hB
    (by decide : Nat.Prime 7) (by decide) hF g).2
  let : Group.IsPerfect SL(2,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let q := QuotientGroup.mk' (center SL(2,F))
  have hgmap : g.range.map q = ⊤ := by
    rw [←MonoidHom.range_comp]
    exact MonoidHom.range_eq_top.mpr hp
  have hg : Function.Surjective g := MonoidHom.range_eq_top.mp (top_le_iff.mp (by
    apply le_of_map_le_of_perfect q (by rw [QuotientGroup.ker_mk']) ⊤ g.range
    rw [hgmap]
    exact le_top))
  intro z
  obtain ⟨b,hb⟩ := hg (e z)
  exact ⟨b,e.injective hb⟩

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The actual nonquasisimple two-core quotient has elementary seven-core of
order 49 and quotient SL₂(7), at either linear-three local residual. -/
theorem local_component_nonquasisimple_seven_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 1 ∨ i = 3) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi i))
    (hLK : s.marking.Li i ≤ K)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    ElementaryModel 7 2 (pCore 7 (K ⧸ pCore 2 K)) ∧
      IsSL ((K ⧸ pCore 2 K) ⧸ pCore 7 (K ⧸ pCore 2 K)) 2 7 := by
  have hidx : LocalIndex i := hi.elim Or.inl (fun hi => .inr (.inl hi))
  have hd : localLinearDimension i = 3 := by rcases hi with rfl | rfl <;> rfl
  let B := s.marking.Li i
  let b : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2) := hd ▸ s.marking.LiCoreEquiv i hidx
  let : Group.IsPerfect B := s.marking.Li_perfect i
  let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (B ⧸ pCore 2 B) := b.isSimpleGroup
  have hb : Nat.card (B ⧸ pCore 2 B) = 168 :=
    (Nat.card_congr b.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card
  let H := s.marking.Gi i
  let C := (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
  let a : K.subgroupOf H ≃* K := subgroupOfEquivOfLe hK.1
  let e : (K ⧸ pCore 2 K) ≃* C :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
      (cComponentTwoCoreQuotientEquiv hK.2)
  have hnC : ¬ IsQuasisimple C := by
    intro hq
    let := hq
    exact hn (IsQuasisimple.of_mulEquiv e.symm)
  let f : B →* C := e.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hLK))
  have hf : IsPGroup 2 f.ker := by
    change IsPGroup 2 (e.toMonoidHom.comp
      ((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hLK))).ker
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ← MonoidHom.comap_ker,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hLK)
  let : Group.IsNilpotent f.ker := hf.isNilpotent
  have hc := Chapter1.Section02.proposition_1_2_1_four_earlier_conclusion
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    (ChapterE.Structure.sqtk_two_quotient
      (h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal i hidx))
      (pCore 2 H) pCore_isPGroup) hK.2
  obtain ⟨hm,hq⟩ := seven_core_of_nonquasisimple hb f
    (Chapter1.RadicalStructure.nonsimple_radical hc hnC)
  let a7 : pCore 7 (K ⧸ pCore 2 K) ≃* pCore 7 C :=
    ((pCore 7 (K ⧸ pCore 2 K)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 7 e))
  refine ⟨⟨a7.trans hm.some⟩,?_⟩
  obtain ⟨F,_,_,hF,⟨q⟩⟩ := hq
  exact ⟨F,inferInstance,inferInstance,hF,
    ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 7 e)).trans q⟩⟩

/-- The E₄₉-by-SL₂(7) source row, on the literal original component quotient. -/
theorem local_component_nonquasisimple_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 1 ∨ i = 3) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi i))
    (hLK : s.marking.Li i ≤ K)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    HasExtension (K ⧸ pCore 2 K) (ElementaryModel 7 2) (fun X _ => IsSL X 2 7) := by
  obtain ⟨hm,hq⟩ := s.local_component_nonquasisimple_seven_core h i hi hK hLK hn
  exact ⟨pCore 7 (K ⧸ pCore 2 K),inferInstance,hm,hq⟩

/-- In the radical row the source product is an equality of the original
embedded subgroups, before quotienting by any core. -/
theorem local_component_nonquasisimple_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 1 ∨ i = 3) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi i))
    (hLK : s.marking.Li i ≤ K)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    K = Chapter1.XiP 7 K ⊔ s.marking.Li i := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hidx : LocalIndex i := hi.elim Or.inl (fun hi => .inr (.inl hi))
  have hd : localLinearDimension i = 3 := by rcases hi with rfl | rfl <;> rfl
  let B := s.marking.Li i
  let Q := K ⧸ pCore 2 K
  let q : K →* Q := QuotientGroup.mk' (pCore 2 K)
  let N := pCore 7 Q
  let r := QuotientGroup.mk' N
  let C := B.subgroupOf K
  let X := Chapter1.xiPIn 7 K
  let J := X ⊔ C
  let a : K.subgroupOf (s.marking.Gi i) ≃* K := subgroupOfEquivOfLe hK.1
  let := hK.2.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsPerfect B := s.marking.Li_perfect i
  let b : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2) := hd ▸ s.marking.LiCoreEquiv i hidx
  let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (B ⧸ pCore 2 B) := b.isSimpleGroup
  have hb : Nat.card (B ⧸ pCore 2 B) = 168 :=
    (Nat.card_congr b.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card
  obtain ⟨hN,hmodel⟩ := s.local_component_nonquasisimple_seven_core h i hi hK hLK hn
  let v := hN.some
  let : IsElementaryAbelian 7 N := {
    toIsMulCommutative := IsMulCommutative.of_comm (fun x y =>
      v.injective (by simp only [map_mul,mul_comm]))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply v.injective
      rw [map_pow,map_one]
      apply congrArg Multiplicative.ofAdd
      funext j
      change (7 : ℕ) • (v x).toAdd j = 0
      have hz : Nat.card (ZMod 7) • (v x).toAdd j = 0 := card_nsmul_eq_zero'
      simpa only [Nat.card_zmod] using hz) }
  let f : B →* Q := q.comp (inclusion hLK)
  let : Group.IsNilpotent f.ker := (show IsPGroup 2 f.ker from by
    change IsPGroup 2 (q.comp (inclusion hLK)).ker
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hLK)).isNilpotent
  have hcover : Function.Surjective (r.comp f) :=
    seven_quotient_covered hb f hmodel
  have hC : (C.map q).map r = ⊤ := by
    rw [map_map]
    have he : (r.comp f).range = C.map (r.comp q) := by
      ext z
      constructor
      · rintro ⟨b,rfl⟩
        exact ⟨⟨b,hLK b.property⟩,b.property,rfl⟩
      · rintro ⟨b,hb,rfl⟩
        exact ⟨⟨b,hb⟩,rfl⟩
    rw [←he]
    exact MonoidHom.range_eq_top.mpr hcover
  have hCN : C.map q ⊔ N = ⊤ := by
    have he := congrArg (comap r) hC
    simpa only [comap_map_eq, r, QuotientGroup.ker_mk', comap_top] using he
  have hX : X.map q = N := by
    rw [Chapter1.xiPIn_map_quotient (by decide : Odd 7)]
    change (omega N (p := 7) 1).map N.subtype = N
    rw [Chapter1.RadicalStructure.omega_top
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 7 N))]
    exact (MonoidHom.range_eq_map _).symm.trans (range_subtype _)
  have hJ : J.map q = ⊤ := by
    rw [Subgroup.map_sup,hX,sup_comm]
    exact hCN
  have hJR : J ⊔ pCore 2 K = ⊤ := by
    have he := congrArg (comap q) hJ
    have hk : q.ker = pCore 2 K := QuotientGroup.ker_mk' _
    simpa only [comap_map_eq,hk,comap_top] using he
  have hRT : K.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hr : (K.subgroupOf (s.marking.Gi i)).pCoreIn 2 ≤
        (T.subtype (s.sylow_le_Gi i hidx) : Subgroup (s.marking.Gi i)) :=
      (pCoreIn_le_of_subnormal 2 hK.2.subnormal).trans
        (pCore_isPGroup.le_sylow_of_normal (T.subtype (s.sylow_le_Gi i hidx)))
    rintro x ⟨k,hk,rfl⟩
    have ha : a.symm k ∈ pCore 2 (K.subgroupOf (s.marking.Gi i)) := by
      have he := pCore_map_iso 2 a.symm
      exact he ▸ mem_map_of_mem a.symm.toMonoidHom hk
    exact hr (mem_map_of_mem _ ha)
  have hRC : pCore 2 K ≤ normalizer (C : Set K) := by
    intro k hk b
    exact s.sylow_normalizes_Li i hidx (hRT (mem_map_of_mem K.subtype hk)) (b : G)
  have hRX : pCore 2 K ≤ normalizer (X : Set K) := by
    let : X.Normal := inferInstance
    rw [normalizer_eq_top]
    exact le_top
  have hRJ : pCore 2 K ≤ normalizer (J : Set K) :=
    (le_inf hRX hRC).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let : J.Normal := normalizer_eq_top_iff.mp (top_unique (hJR ▸ sup_le J.le_normalizer hRJ))
  let : Group.IsNilpotent (K ⧸ J) :=
    (isPGroup_quotient_of_sup_eq_top J (pCore 2 K) pCore_isPGroup hJR).isNilpotent
  have ht : J = ⊤ := top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ J)
  have he := congrArg (map K.subtype) ht
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hLK,
    ←MonoidHom.range_eq_map,range_subtype] at he
  exact he.symm

/-- The full radical alternative at the point, including the actual Ξ₇ product. -/
theorem local_point_component_radical_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    LocalComponentAlternative s 1 K :=
  .radical rfl (s.local_component_nonquasisimple_product h 1 (.inl rfl) hK hLK hn)
    (s.local_component_nonquasisimple_model h 1 (.inl rfl) hK hLK hn)

/-- At the three-space, full natural action settles the quasisimple row;
the only possible strict component is the actual Ξ₇ extension. The source
ambient argument still has to exclude this latter row. -/
theorem local_three_component_equal_or_radical
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 3))
    (hLK : s.marking.Li 3 ≤ K) :
    s.marking.Li 3 = K ∨
      (K = Chapter1.XiP 7 K ⊔ s.marking.Li 3 ∧
        HasExtension (K ⧸ pCore 2 K) (ElementaryModel 7 2) (fun X _ => IsSL X 2 7)) := by
  by_cases hq : IsQuasisimple (K ⧸ pCore 2 K)
  · let := hq
    exact .inl (s.local_component_eq_of_quasisimple 3 (.inl rfl) hK hLK)
  · exact .inr ⟨s.local_component_nonquasisimple_product h 3 (.inr rfl) hK hLK hq,
      s.local_component_nonquasisimple_model h 3 (.inr rfl) hK hLK hq⟩
end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
