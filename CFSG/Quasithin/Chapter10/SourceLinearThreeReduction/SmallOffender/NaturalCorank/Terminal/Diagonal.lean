module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.Terminal.Pair
public import Theory.GroupTheory.TwoFixedLinesIrreducible
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Diagonal involutions before the weak-closure conclusion

The full module is the direct product of its two exchanged moved factors.
A T-fixed point therefore has unique coordinates fixed by N_T(L); exchange
forces both coordinates of a nonzero point to be nonzero. The two-group
fixed-point theorem constructs such a point, and elementary abelianness gives
its involution order. The prescribed-point version feeds the terminal witness.

This adapts Geometry.Pair's diagonal construction to the earlier natural
geometry, removing its unused survivor and weak-closure premises.
Source: Aschbacher--Smith, 10.2.11--12, printed pp.753--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}

/-- Each nonzero T-fixed point of the full module has two nonzero factor coordinates, both fixed by N_T(L). -/
theorem natural_diagonal_of_central_point
    (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (z₀ : G) (hzV : z₀ ∈ D.fullModule)
    (hzT : z₀ ∈ centralizer ((T : Subgroup G) : Set G)) (hz₀ : z₀ ≠ 1) :
    ∃ a b : G, a ∈ ⁅D.fullModule,L⁆ ∧
      b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ∧
      a ≠ 1 ∧ b ≠ 1 ∧
      a ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G) ∧
      b ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G) ∧
      a * b = z₀ := by
  let A := ⁅D.fullModule,L⁆
  let B := A.map (MulAut.conj t).toMonoidHom
  let V := D.fullModule
  let : IsElementaryAbelian 2 V := by
    change IsElementaryAbelian 2 D.fullModule
    rw [m.full_eq_local]
    exact D.module_elementary
  have hgen : V = A ⊔ B :=
    source_nonnormal_fullModule_eq_moved_pair D hn ht (m.crossed t ht htn)
  have hAV : A ≤ V := le_sup_left.trans_eq hgen.symm
  have hBV : B ≤ V := le_sup_right.trans_eq hgen.symm
  have hzero := moved_fixed_eq_bot_of_full_fixed_eq_bot m hn hz
  have hd : Disjoint A B := disjoint_iff.mpr (bot_unique
    ((inf_le_inf_left A (m.crossed t ht htn)).trans_eq hzero))
  have hc : A ≤ centralizer (B : Set G) := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨b,hBV hb⟩ : V) ⟨a,hAV ha⟩)
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  let z : (V ⊓ centralizer ((T : Subgroup G) : Set G) : Subgroup G) := ⟨z₀,hzV,hzT⟩
  have hzne' : (z : G) ≠ 1 := hz₀
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  have hzAB : (z : G) ∈ A ⊔ B := hgen ▸ z.property.1
  obtain ⟨⟨a,b⟩,hab⟩ := e.surjective ⟨z,hzAB⟩
  have hab' : (a:G) * (b:G) = (z:G) := (he a b).symm.trans (congrArg Subtype.val hab)
  have hfix (t : G) (ht : t ∈ (T : Subgroup G)) : (MulAut.conj t) (z:G) = (z:G) := by
    change t * (z:G) * t⁻¹ = (z:G)
    rw [z.property.2 t ht, mul_inv_cancel_right]
  have hane : (a:G) ≠ 1 := by
    intro ha
    have hzb : (z:G) ∈ B := by
      have hbz : (b:G) = (z:G) := by simpa only [ha, one_mul] using hab'
      exact hbz ▸ b.property
    have hza : (z:G) ∈ A := by
      obtain ⟨x,hx,hxz⟩ := hzb
      have hh : x = (z:G) := (MulAut.conj t).injective
        (hxz.trans (hfix t ht).symm)
      exact hh ▸ hx
    exact hzne' (mem_bot.mp (hd.eq_bot ▸ (show (z:G) ∈ A ⊓ B from ⟨hza,hzb⟩)))
  have hbne : (b:G) ≠ 1 := by
    intro hb
    have hza : (z:G) ∈ A := by
      have haz : (a:G) = (z:G) := by simpa only [hb, mul_one] using hab'
      exact haz ▸ a.property
    have hzb : (z:G) ∈ B := by
      have hh := mem_map_of_mem (MulAut.conj t).toMonoidHom hza
      change (MulAut.conj t) (z:G) ∈ B at hh
      rwa [hfix t ht] at hh
    exact hzne' (mem_bot.mp (hd.eq_bot ▸ (show (z:G) ∈ A ⊓ B from ⟨hza,hzb⟩)))
  have hNW : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G) := by
    intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.fullModule,L⁆).map (MulAut.conj r).toMonoidHom = ⁅D.fullModule,L⁆
    have hV : D.fullModule.map (MulAut.conj r).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp
        (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T hr.1))
    have hL : L.map (MulAut.conj r).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp hr.2
    rw [map_commutator,hV,hL]
  have hNB : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (B : Set G) := by
    have hBA : B ≤ normalizer (A : Set G) :=
      ((hBV.trans V.le_centralizer).trans (centralizer_le hAV)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hf : V ⊓ centralizer (L : Set G) = B := by
      rw [hgen,sup_comm,inf_centralizer_sup_of_centralizing B A L hBA (m.crossed t ht htn),
        hzero,sup_bot_eq]
    rw [← hf]
    exact (le_inf (inf_le_left.trans hTV)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hfixed (t : G) (ht : t ∈ (T : Subgroup G) ⊓ normalizer (L : Set G)) :
      (MulAut.conj t) (a:G) = a ∧ (MulAut.conj t) (b:G) = b := by
    have ha := (mem_normalizer_iff.mp (hNW ht) a).mp a.property
    have hb := (mem_normalizer_iff.mp (hNB ht) b).mp b.property
    have hh : (MulAut.conj t) (a:G) * (MulAut.conj t) (b:G) = (a:G) * (b:G) := by
      rw [← map_mul, hab', hfix t ht.1]
    have hp : ((⟨(MulAut.conj t) (a:G),ha⟩ : A),(⟨(MulAut.conj t) (b:G),hb⟩ : B)) =
        (a,b) := mul_injective_of_disjoint hd hh
    exact ⟨congrArg (fun p : A × B => (p.1:G)) hp,
      congrArg (fun p : A × B => (p.2:G)) hp⟩
  refine ⟨a,b,a.property,b.property,hane,hbne,?_,?_,?_⟩
  · intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (hfixed t ht).1
  · intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (hfixed t ht).2
  · exact hab'

/-- Construct a central diagonal involution before any weak-closure equality or survivor record is available. -/
theorem exists_natural_diagonal
    (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ a b : G, a ∈ ⁅D.fullModule,L⁆ ∧
      b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ∧
      a ≠ 1 ∧ b ≠ 1 ∧
      a ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G) ∧
      b ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G) ∧
      a * b ∈ centerIn (T : Subgroup G) ∧ orderOf (a * b) = 2 := by
  let V := D.fullModule
  let : IsElementaryAbelian 2 V := by
    change IsElementaryAbelian 2 D.fullModule
    rw [m.full_eq_local]
    exact D.module_elementary
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  have hVne : V ≠ ⊥ := by
    change D.fullModule ≠ ⊥
    rw [m.full_eq_local]
    exact D.module_ne_bot
  obtain ⟨z,hzne⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centralizer_ne_bot_of_pGroups (T : Subgroup G) V T.isPGroup'
      (IsElementaryAbelian.isPGroup 2 V) hTV hVne)
  have hzne' : (z : G) ≠ 1 := fun h => hzne (Subtype.ext h)
  obtain ⟨a,b,ha,hb,ha1,hb1,haf,hbf,hab⟩ := natural_diagonal_of_central_point
    m hn ht htn hz z z.property.1 z.property.2 hzne'
  refine ⟨a,b,ha,hb,ha1,hb1,haf,hbf,?_,?_⟩
  · rw [hab]
    exact ⟨D.module_le_sylow (m.full_eq_local ▸ z.property.1),z.property.2⟩
  · rw [hab]
    exact orderOf_eq_prime_iff.mpr
      ⟨elemPow_eq_one_of_isElementaryAbelian (p := 2) (z:G) z.property.1,hzne'⟩

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
