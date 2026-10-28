module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Movement
public import Theory.Mathieu.M22.Properties.TwoLocalSeven
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Point-core containment for the central Mathieu22 cover

Map the original seed and point residual through the actual component
quotient and then its central three-quotient. The seed stays elementary;
the point residual retains its factor of seven. Restricting the original
Sylow subgroup through relative normality supplies a full Sylow subgroup
normalizing the seed image. A nonzero image would thus give a two-local
Sylow overgroup of M₂₂ divisible by seven, contradicting its native bound.
The odd central kernel is injective on the seed image, so the seed already
vanishes in the component's two-core quotient.

PointCore.Complete uses this row in the full source catalogue. It assumes
neither Y ≤ K₁ nor a refined point-component alternative.
Source: Aschbacher--Smith 12.5.8(1), printed p.820, and A.3.6, pp.43--45.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The actual triple-Mathieu22 quotient puts the unchanged seed in the point core. -/
theorem seed_le_point_core_of_mathieu_cover {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K) (hKG : K ≤ s.marking.Gi 1)
    (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : IsM22Cover (K ⧸ pCore 2 K)) : V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  let Q := K ⧸ pCore 2 K
  let q := QuotientGroup.mk' (pCore 2 K)
  obtain ⟨z⟩ := hm.2.1
  obtain ⟨e⟩ := hm.2.2
  let f : Q →* Sporadic.Mathieu.M22 := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hc : Nat.card f.ker = 3 := by rw [hk]; simpa using Nat.card_congr z.toEquiv
  have hVK : V ≤ K := s.seed_le_point_residual.trans hLK
  let A := V.subgroupOf K
  let E := A.map q
  let C := (s.marking.Li 1).subgroupOf K
  let B := C.map q
  let := D.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hVK
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hBE : B ≤ normalizer (E : Set Q) := by
    apply (map_mono (f := q) ?_).trans (A.le_normalizer_map q)
    intro c hc x
    exact ((s.marking.Li_le_L 1).trans D.normalizes) hc (x : G)
  let K₀ := K.subgroupOf (s.marking.Gi 1)
  let a : K₀ ≃* K := subgroupOfEquivOfLe hKG
  let := hn
  obtain ⟨P,hP⟩ := (T.subtype s.sylow_le_G₁).exists_subgroupOf_eq_of_normal K₀
  let P₀ := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hP₀ : (P₀ : Subgroup K) ≤ normalizer (A : Set K) := by
    rintro _ ⟨x,hx,rfl⟩ v
    have hxT : (x.val.val : G) ∈ T := by rw [hP] at hx; exact hx
    exact s.normalizes ((show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) hxT) (v : G)
  let S := (P₀.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)).mapSurjective
    (f := f) hf
  have hS : (S : Subgroup Sporadic.Mathieu.M22) ≤ normalizer (E.map f : Set _) :=
    (map_mono ((map_mono hP₀).trans (A.le_normalizer_map q))).trans (E.le_normalizer_map f)
  have h7C : 7 ∣ Nat.card C := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hLK).toEquiv]
    apply dvd_trans (b := Nat.card (s.marking.Li 1 ⧸ pCore 2 (s.marking.Li 1)))
    · rw [Nat.card_congr (s.marking.LiCoreEquiv 1 (.inl rfl)).toEquiv]
      change 7 ∣ Nat.card SL(3,ZMod 2)
      rw [Atlas.Comparisons.Exceptional.sl3Two_card]
      decide
    · exact card_dvd_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have h7B : 7 ∣ Nat.card B := by
    let g := q.subgroupMap C
    have hker : IsPGroup 2 g.ker := by
      rw [ker_subgroupMap, QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    obtain ⟨n,hn⟩ := hker.exists_card_dvd_pow
    have hcop : Nat.Coprime 7 (Nat.card g.ker) :=
      ((show Nat.Coprime 7 2 by decide).pow_right n).coprime_dvd_right hn
    have he := g.ker.card_mul_index
    rw [index_ker, MonoidHom.range_eq_top.mpr (q.subgroupMap_surjective C),
      Nat.card_congr Subgroup.topEquiv.toEquiv] at he
    exact hcop.dvd_of_dvd_mul_left (he.symm ▸ h7C)
  have h7 : 7 ∣ Nat.card (B.map f) := by
    let g := f.comp B.subtype
    have hg : Nat.card g.ker ∣ Nat.card f.ker := by
      let j : g.ker →* f.ker := {
        toFun x := ⟨x.val.val,x.property⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
      exact card_dvd_of_injective j
        (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : f.ker => (t : Q)) h)))
    have hcop : Nat.Coprime 7 (Nat.card g.ker) :=
      (show Nat.Coprime 7 (Nat.card f.ker) by rw [hc]; decide).coprime_dvd_right hg
    have he := g.ker.card_mul_index
    rw [index_ker] at he
    have hrg : g.range = B.map f := by simp [g, MonoidHom.range_comp]
    rw [hrg] at he
    exact hcop.dvd_of_dvd_mul_left (he.symm ▸ h7B)
  have hzero : E.map f = ⊥ := by
    by_contra hz
    have hloc : IsTwoLocal (normalizer (E.map f : Set Sporadic.Mathieu.M22)) :=
      ⟨E.map f,hz,(IsElementaryAbelian.isPGroup 2 E).map f,rfl⟩
    exact Sporadic.Mathieu.M22TwoLocalOrders.not_seven_dvd_card_twoLocal S _ hloc hS
      (h7.trans (card_dvd_of_le ((map_mono hBE).trans (E.le_normalizer_map f))))
  have hE : E = ⊥ := by
    have hinj := Subgroup.injective_comp_subtype_of_coprime_ker f
      (show Nat.Coprime 2 (Nat.card f.ker) by rw [hc]; decide) E
      (IsElementaryAbelian.isPGroup 2 E)
    apply eq_bot_iff.mpr
    intro x hx
    have hh : f x = 1 := (show f x ∈ (⊥ : Subgroup Sporadic.Mathieu.M22) from
      hzero ▸ mem_map_of_mem f hx)
    have hh' : (f.comp E.subtype) ⟨x,hx⟩ = (f.comp E.subtype) 1 := by
      simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, OneMemClass.coe_one,map_one] using hh
    exact congrArg Subtype.val (hinj (a₁ := ⟨x,hx⟩) (a₂ := 1) hh')
  have hA : A ≤ pCore 2 K := by
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff A).mp hE
  have hcore : V ≤ K.pCoreIn 2 := by
    intro v hv
    exact ⟨⟨v,hVK hv⟩,hA hv,rfl⟩
  exact hcore.trans (pCoreIn_mono_of_normalizes hKG
    ((normal_subgroupOf_iff_le_normalizer hKG).mp hn))

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
