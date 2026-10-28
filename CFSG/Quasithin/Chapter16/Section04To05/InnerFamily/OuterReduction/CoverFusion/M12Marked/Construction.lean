module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.M12Marked.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.Mathieu12.ComponentFusion
public import Theory.Mathieu.M12.SylowCenterSquares
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# A marked involution in the actual outer M₁₂ residual

The exact earlier 16.1.5(4) table identifies the fixed subgroup with C₂ × A₅.
Embed the A₅ factor and take its explicit double transposition. Perfectness
places it in O² of the fixed subgroup. The checked `ComponentFusion` argument
makes it a square in M₁₂, so `SylowCenterSquares` conjugates it to the marked
central involution z and proves two-centrality. Its centralizer in the full
fixed subgroup has order eight, by a finite A₅ calculation.

Restrict the original automorphism to the centralizer of this involution,
then transport it to the concrete C_M₁₂(z). Its square and fixed subgroup
are preserved. `M12CentralizerDisplacement` is precisely the remaining
local calculation that supplies the conjugator; it is not asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(4), printed p.1171; proof of 16.4.9(2), pp.1190–1191.
Only exact earlier table clauses are used to construct the residual mark.
-/

public section

open Subgroup Sporadic.Mathieu Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion
open LiePreliminaries DoubleCoverCentralizer OtherPreliminaries.Mathieu

private def a5mark : A5 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    change Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) = 1
    decide +kernel⟩
private theorem a5mark_order : orderOf a5mark = 2 := by
  apply orderOf_eq_prime <;> decide +kernel
private theorem a5mark_centralizer_card : Nat.card (centralizer ({a5mark} : Set A5)) = 4 := by
  let : DecidablePred (fun y : A5 => y ∈ centralizer ({a5mark} : Set A5)) :=
    fun y => decidable_of_iff (y * a5mark = a5mark * y) mem_centralizer_singleton_iff.symm
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem a5_residual : pResidual 2 A5 = ⊤ := by
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  apply (pResidual_eq_top_iff 2 _).mpr
  intro N hN hp
  let := hN
  have hsub : Subsingleton (A5 ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private noncomputable def centralizerEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (v : G) : centralizer ({v} : Set G) ≃* centralizer ({e v} : Set H) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_centralizer_singleton e v))

private theorem product_mark_centralizer_card :
    Nat.card (centralizer ({(1, a5mark)} : Set (C2 × A5))) = 8 := by
  have he : centralizer ({(1, a5mark)} : Set (C2 × A5)) =
      (⊤ : Subgroup C2).prod (centralizer ({a5mark} : Set A5)) := by
    ext y
    simp [mem_prod, mem_centralizer_singleton_iff, Prod.ext_iff]
  rw [he, Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod,
    Nat.card_congr (topEquiv : (⊤ : Subgroup C2) ≃* C2).toEquiv, a5mark_centralizer_card]
  norm_num [C2, Nat.card_eq_fintype_card]

/-- The A₅ factor supplies an actual residual involution, its two-central
mark, a conjugator from the fixed Sylow-center representative, and the exact
order of its centralizer inside the full fixed subgroup. -/
theorem m12_marked_residual_involution
    (table : ∀ r : MulAut M12, orderOf r = 2 → M12InvolutionAlternative r)
    (b : MulAut M12) (hb : orderOf b = 2) (hout : ¬ ∃ s : M12, b = MulAut.conj s) :
    ∃ v : b.fixedSubgroup, (v : M12) ∈ fixedTwoResidual M12 b ∧
      orderOf (v : M12) = 2 ∧ TwoCentral (v : M12) ∧
      (∃ g : M12, MulAut.conj g M12SmallPair.z = (v : M12)) ∧
      Nat.card (centralizer ({v} : Set b.fixedSubgroup)) = 8 := by
  have he : Nonempty (b.fixedSubgroup ≃* C2 × A5) := by
    rcases table b hb with ⟨hi, _⟩ | ⟨_, he⟩
    · exact (hout hi).elim
    · exact he
  obtain ⟨e⟩ := he
  let f : A5 →* b.fixedSubgroup := e.symm.toMonoidHom.comp (MonoidHom.inr C2 A5)
  have hf : Function.Injective f := by
    intro x y h
    exact congrArg Prod.snd (e.symm.injective h)
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let v : b.fixedSubgroup := f a5mark
  have hv : (v : M12) ∈ fixedTwoResidual M12 b := by
    refine ⟨v, map_pResidual_le 2 f ?_, rfl⟩
    exact ⟨a5mark, by rw [a5_residual]; trivial, rfl⟩
  have hv2 : orderOf (v : M12) = 2 :=
    (orderOf_coe v).trans ((orderOf_injective f hf a5mark).trans a5mark_order)
  have hsquare : ∃ y : M12, y ^ 2 = (v : M12) :=
    FourGroupTransfer.SylowModels.Mathieu12.fixed_perfect_involution_square
      table b hb f hf a5mark a5mark_order
  have hconj := M12SylowCenters.square_involution_conjugate (v : M12) hv2 hsquare
  obtain ⟨S, hS⟩ := M12SylowCenters.exists_sylow_center_of_square (v : M12) hv2 hsquare
  have hmem : (v : M12) ∈ (center S).map (S : Subgroup M12).subtype := by
    rw [hS]
    exact mem_zpowers (v : M12)
  obtain ⟨w, hw, hew⟩ := hmem
  refine ⟨v, hv, hv2, ⟨S, hew ▸ w.property, ?_⟩, hconj, ?_⟩
  · have heq : (⟨(v : M12), hew ▸ w.property⟩ : S) = w := Subtype.ext hew.symm
    rw [heq]
    exact hw
  · rw [Nat.card_congr (centralizerEquiv e v).toEquiv]
    change Nat.card (centralizer ({e (e.symm (1, a5mark))} : Set (C2 × A5))) = 8
    rw [e.apply_symm_apply]
    exact product_mark_centralizer_card

private noncomputable def restrictCentralizer {G : Type*} [Group G]
    (b : MulAut G) (v : b.fixedSubgroup) : MulAut (centralizer ({(v : G)} : Set G)) :=
  (centralizerEquiv b v).trans (MulEquiv.subgroupCongr (by
    rw [(MulAut.mem_fixedSubgroup b v).mp v.property]))

private noncomputable def fixedRestrictionEquiv {G : Type*} [Group G]
    (b : MulAut G) (v : b.fixedSubgroup) :
    (restrictCentralizer b v).fixedSubgroup ≃* centralizer ({v} : Set b.fixedSubgroup) where
  toFun x := ⟨⟨x.val.val, by
    have h := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)
    exact (MulAut.mem_fixedSubgroup b _).mpr h⟩, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
  invFun x := ⟨⟨x.val.val, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩, by
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      apply Subtype.ext
      exact (MulAut.mem_fixedSubgroup b _).mp x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The local displacement equation transports to the original automorphism
and original involution; all centralizers and fixed subgroups are literal. -/
theorem m12_conjugator_of_centralizerDisplacement (hlocal : M12CentralizerDisplacement)
    (b : MulAut M12) (hb : b ^ 2 = 1) (v : b.fixedSubgroup)
    (hc : Nat.card (centralizer ({v} : Set b.fixedSubgroup)) = 8)
    (g : M12) (hg : MulAut.conj g M12SmallPair.z = (v : M12)) :
    ∃ l : M12, b l * l⁻¹ = (v : M12) := by
  let d := restrictCentralizer b v
  let e : M12SmallPair.firstParabolic ≃* centralizer ({(v : M12)} : Set M12) :=
    (centralizerEquiv (MulAut.conj g) M12SmallPair.z).trans
      (MulEquiv.subgroupCongr (by rw [hg]))
  let a := MulAut.congr e.symm d
  have hd2 : d ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change b (b (x : M12)) = (x : M12)
    have h := congrArg (fun f : MulAut M12 => f (x : M12)) hb
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have ha2 : a ^ 2 = 1 := by
    rw [← map_pow, hd2, map_one]
  have hac : Nat.card a.fixedSubgroup = 8 := by
    rw [← Nat.card_congr (MulAut.fixedSubgroupCongr e.symm d).toEquiv,
      Nat.card_congr (fixedRestrictionEquiv b v).toEquiv]
    exact hc
  obtain ⟨l, hl⟩ := hlocal a ha2 hac
  let z0 : M12SmallPair.firstParabolic :=
    ⟨M12SmallPair.z, mem_centralizer_singleton_iff.mpr rfl⟩
  have hez : (e z0 : M12) = (v : M12) := hg
  have hl' : a l * l⁻¹ = z0 := Subtype.ext hl
  have h := congrArg e hl'
  rw [map_mul, map_inv] at h
  have hed : e (a l) = d (e l) := by
    change e (e.symm (d (e l))) = d (e l)
    rw [e.apply_symm_apply]
  rw [hed] at h
  exact ⟨e l, (congrArg Subtype.val h).trans hez⟩

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion
