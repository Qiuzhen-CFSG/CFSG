module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupNatural
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.Action
public import Theory.GroupTheory.ConjugateSpanCentralQuotient

/-!
# Cartan movement on the literal parity quotient

The central image of A in H₁/O₂(H₁) makes AO₂(H₁) normal in H₁.
The original F.8 action identifies O₂(H₁) with the kernel on U/Z₁.
Since the Cartan moves the selected natural V, the conjugate-span
argument proves U = [U,A]Z₁, keeping both original quotient subgroups.

The final constructor derives the point order, central Cartan image,
moved quotient and binary rank required by Seed. Natural marking,
global TI and F.8 geometry remain explicit source obligations owned
by qt-d-1222-linear-field-parity. No unconditional parity result is
asserted here.

Source: Aschbacher–Smith 5.1.17, printed pp.640–641 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

/-- The actual H₁-span is generated modulo Z₁ by its Cartan commutators. -/
theorem fundamental_span_cartan_moved
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hn : 1 < n)
    (c : CartanPair T L H A B) (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hf : (setup T L D.moduleSubgroup H A).Hypothesis)
    (hc : (A.subgroupOf (H ⊔ A)).map
        (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))) ≤
      center ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G))) :
    ⁅(setup T L D.moduleSubgroup H A).U,A⁆ ⊔
        (setup T L D.moduleSubgroup H A).V₁ =
      (setup T L D.moduleSubgroup H A).U := by
  let E := setup T L D.moduleSubgroup H A
  let J := H ⊔ A
  let q := QuotientGroup.mk' (pCore 2 J)
  let N := ((A.subgroupOf J).map q).comap q
  let : ((A.subgroupOf J).map q).Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hc hx) g, mul_inv_cancel_right]
    exact hx⟩
  let : N.Normal := inferInstance
  have hN : N.map J.subtype = A ⊔ J.pCoreIn 2 := by
    rw [show N = A.subgroupOf J ⊔ pCore 2 J from by
      change ((A.subgroupOf J).map q).comap q = _
      rw [comap_map_eq,QuotientGroup.ker_mk'],Subgroup.map_sup,
      map_subgroupOf_eq_of_le (show A ≤ J from le_sup_right)]
    rfl
  have hJN : J ≤ normalizer ((A ⊔ J.pCoreIn 2 : Subgroup G) : Set G) := by
    have hh := le_normalizer_map (H := N) J.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, hN] at hh
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans hf.local_le
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow J (T.subtype hTJ)).trans
      (map_subgroupOf_eq_of_le hTJ).le
  have hUQ : ⁅E.U,E.QH⁆ ≤ E.V₁ :=
    (le_core_iff_commutator_le hf E.QH (pCoreIn_le 2 J)).mp le_rfl
  exact commutator_span_sup_of_normal_modulo D.moduleSubgroup J A (J.pCoreIn 2)
    E.V₁ le_sup_right (pCoreIn_le 2 J) hJN
    (hQT.trans D.sylow_normalizes_module)
    (fundamental_cartan_commutator D hTL hpsl hn c hnat).symm
    (point_le_span hf) hUQ hf.H_le

/-- Assemble the parity seed with its numerical and movement fields derived. -/
theorem seed_of_fundamental_geometry
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hf : (setup T L D.moduleSubgroup H A).Hypothesis)
    (hti : ∀ g : G,
      (setup T L D.moduleSubgroup H A).V₁ ⊓
          (setup T L D.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (setup T L D.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom =
          (setup T L D.moduleSubgroup H A).V₁) :
    Nonempty (Seed T L H A n) := by
  have hc := cartan_image_central_of_odd h hH c hodd hK hnf hm
  exact ⟨{
    V := D.moduleSubgroup
    fundamental := D
    module_eq := rfl
    natural := hnat
    f8 := hf
    point_card := fundamental_point_card D h.sylow_normalizes h.linear hodd hnat
    point_TI := hti
    cartan_central := hc
    moved := fundamental_span_cartan_moved D h.sylow_normalizes h.linear h.exponent c hnat hf hc
    quotient_rank := (odd_join_quotient_two_rank h hH c hodd hK hnf hm).le }⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
