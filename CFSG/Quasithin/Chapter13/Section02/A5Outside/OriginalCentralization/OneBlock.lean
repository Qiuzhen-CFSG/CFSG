module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.TwoBlocks
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableCores
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreFrattini
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.Representation.BinaryPermutation.FiveBorelFixed
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SeedKnownSimple
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer

/-!
# Excluding either single block in the original outside pair

For commuting original natural modules, a block's core commutators fix
that block and move the opposite module. A nontrivial Sylow-normalized
subgroup of the latter contains its flag line. The two natural modules
must therefore be disjoint. Relative block displacement now makes the
opposite module centralize a Sylow subgroup of the block.

C.1.13(c) splits the local core into its natural module and its component
centralizer, retaining the entire central factor. A Sylow subgroup of A₅
fixes at most two vectors of the marked natural module, so the opposite
module has a component-fixed hyperplane. The existing full 13.2.3(2)
centralizer bound on that same invariant hyperplane contradicts original
outside placement. Either relative block thus forces noncommuting modules.

SourceAssembly/NonsolvableOneBlock constructs the residual elementary
four-group lift and invokes original 5.2.3. No block subnormality in the
larger join, central-factor vanishing or component-core equality is used.
Source: Aschbacher--Smith C.1.7--13, pp.123--125; 13.2.3(2), p.879;
and the nonsolvable step of 13.2.8(1), p.880.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterC
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

private theorem line_le_of_normalized_ne_bot
    (e : Context T K W W₁ W₂ W₃) {A : Subgroup G}
    (hAW : A ≤ W) (hne : A ≠ ⊥)
    (hn : (T : Subgroup G) ≤ normalizer (A : Set G)) : W₁ ≤ A := by
  have hmeet := inf_centerIn_ne_bot T.isPGroup' hne (hAW.trans e.chosen.le_sylow) hn
  have hle : A ⊓ centerIn (T : Subgroup G) ≤ W₁ := by
    rw [←e.flag.module_fixed_eq_line]
    exact le_inf (inf_le_left.trans hAW) (inf_le_right.trans inf_le_right)
  have hc : Nat.card (A ⊓ centerIn (T : Subgroup G) : Subgroup G) = 2 := by
    have hd := card_dvd_of_le hle
    rw [e.flag.one_card] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
    · exact (hmeet (eq_bot_of_card_le _ (by omega))).elim
    · exact hh
  have heq := eq_of_le_of_card_ge hle (by rw [e.flag.one_card,hc])
  exact heq.ge.trans inf_le_left

/-- In a commuting original pair, one block already forces disjoint natural modules. -/
theorem one_block_modules_disjoint
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hbL : IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))))
    (hVW : V ≤ centralizer (W : Set G))
    (hQW : ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (W : Set G)) :
    Disjoint V W := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hWQ : W ≤ Q := by
    rw [show Q = (T : Subgroup G) ⊓ centralizer (V : Set G) from
      (d.sylow_centralizer d.normalizes_L).symm]
    exact le_inf e.chosen.le_sylow (le_centralizer_iff.mp hVW)
  have hcomm : ⁅Q,W⁆ ≠ ⊥ := fun hh => hQW (commutator_eq_bot_iff_le_centralizer.mp hh)
  have hF : ⁅Q,Q⁆ ≤ centralizer (L : Set G) := by
    let : Fact (IsPGroup 2 Q) := ⟨isPGroup_pCoreIn 2 _⟩
    have h := map_mono (f := Q.subtype) (commutator_le_frattini_of_isPGroup (p := 2) (R := Q))
    rw [map_subtype_commutator] at h
    exact h.trans (relative_core_frattini_centralizes le_sup_left hbL)
  have hCne : W ⊓ centralizer (L : Set G) ≠ ⊥ := by
    intro hh
    apply hcomm
    apply bot_unique
    exact (le_inf (le_normalizer_iff_commutator_le_right.mp (hQT.trans e.flag.T_normalizes))
      ((commutator_mono le_rfl hWQ).trans hF)).trans hh.le
  have hW₁ : W₁ ≤ centralizer (L : Set G) :=
    (line_le_of_normalized_ne_bot e inf_le_left hCne
      ((le_inf e.flag.T_normalizes (d.normalizes_L.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf)).trans inf_le_right
  apply disjoint_iff.mpr
  by_contra hh
  have hline : W₁ ≤ V ⊓ W := line_le_of_normalized_ne_bot e inf_le_right hh
    ((le_inf d.flag.T_normalizes e.flag.T_normalizes).trans inf_normalizer_le_normalizer_inf)
  have hz : W₁ = ⊥ := bot_unique ((le_inf (hline.trans inf_le_left) hW₁).trans
    d.flag.module.fixed_eq_bot.le)
  have hc := e.flag.one_card
  rw [hz,Nat.card_eq_fintype_card] at hc
  simp at hc
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

private theorem exists_component_sylow (d : Context T L V V₁ V₂ V₃) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype ≤ (T : Subgroup G) := by
  let J := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
  obtain ⟨S,hS⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal A
  let a : A ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  refine ⟨S.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
  rintro x ⟨l,⟨s,hs,rfl⟩,rfl⟩
  have hh := hS ▸ hs
  exact hh

private theorem component_sylow_fixed_card_le_two (d : Context T L V V₁ V₂ V₃)
    (P : Sylow 2 L) :
    Nat.card (V ⊓ centralizer ((P : Subgroup L).map L.subtype : Set G) : Subgroup G) ≤ 2 := by
  classical
  let F := V ⊓ centralizer ((P : Subgroup L).map L.subtype : Set G)
  let R := P.mapSurjective d.flag.module.onto
  have hfix (v : Multiplicative (BinaryPermutation.core (Fin 5)))
      (hv : d.flag.module.map v ∈ centralizer ((P : Subgroup L).map L.subtype : Set G)) :
      v.toAdd ∈ Representation.BinaryOffender.fixedSpace
        (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) R := by
    rintro ⟨r,⟨p,hp,rfl⟩⟩
    apply Multiplicative.ofAdd.injective
    apply d.flag.module.injective
    change d.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (d.flag.module.action p).val v.toAdd)) = d.flag.module.map v
    rw [←d.flag.module.equivariant]
    exact mul_inv_eq_iff_eq_mul.mpr (hv p (mem_map_of_mem L.subtype hp))
  have hunique (x y : F) (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
    obtain ⟨v,hv⟩ := d.flag.module.range_eq.ge x.property.1
    obtain ⟨w,hw⟩ := d.flag.module.range_eq.ge y.property.1
    have hv0 : v.toAdd ≠ 0 := fun hz => hx (Subtype.ext (by rw [←hv,show v=1 from hz,map_one];rfl))
    have hw0 : w.toAdd ≠ 0 := fun hz => hy (Subtype.ext (by rw [←hw,show w=1 from hz,map_one];rfl))
    have he := BinaryPermutation.FiveBorelFixed.sylow_fixed_unique R v.toAdd w.toAdd hv0 hw0
      (hfix v (hv.symm ▸ x.property.2)) (hfix w (hw.symm ▸ y.property.2))
    exact Subtype.ext (hv.symm.trans ((congrArg d.flag.module.map (show v=w from he)).trans hw))
  let f : F → Bool := fun x => if x=1 then false else true
  have hi : Function.Injective f := by
    intro x y he
    by_cases hx : x=1
    · by_cases hy : y=1
      · exact hx.trans hy.symm
      · simp [f,hx,hy] at he
    · by_cases hy : y=1
      · simp [f,hx,hy] at he
      · exact hunique x y hx hy
  have hh := Nat.card_le_card_of_injective f hi
  exact hh.trans_eq (by simp [Nat.card_eq_fintype_card])
end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Subgroup Theory.GroupTheory ChapterC Section05.A5Source
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

theorem one_block_fixed_hyperplane
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hb : IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))))
    (ha : IsAlternatingBlock L 5)
    (hVW : V ≤ centralizer (W : Set G))
    (hm : ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (W : Set G)) :
    ∃ U : Subgroup G, U ≤ W ∧ Nat.card U = 8 ∧
      (T : Subgroup G) ≤ normalizer (U : Set G) ∧ U ≤ centralizer (L : Set G) := by
  classical
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let C := Q ⊓ centralizer (L : Set G)
  have hQT : Q ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hWQ : W ≤ Q := by
    rw [show Q = (T : Subgroup G) ⊓ centralizer (V : Set G) from
      (d.sylow_centralizer d.normalizes_L).symm]
    exact le_inf e.chosen.le_sylow (le_centralizer_iff.mp hVW)
  have hdis := one_block_modules_disjoint d e hb hVW hm
  have hVL := d.blockU_eq_module_of_short ha.2.1
  have hsplit : Q = V ⊔ C := by
    have hh := ha.normalizer_twoCore_eq_module_sup_centralizer
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer d.normalizes_L)
    rwa [hVL] at hh
  obtain ⟨S,hST⟩ := d.exists_component_sylow
  let R := (S : Subgroup L).map L.subtype
  have hRL : R ≤ L := map_subtype_le _
  have hWR : W ≤ centralizer (R : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply (le_inf ?_ ?_).trans hdis.eq_bot.le
    · exact (commutator_mono hWQ hRL).trans
        ((relative_core_commutator_le_blockU le_sup_left hb).trans_eq hVL)
    · exact le_normalizer_iff_commutator_le_left.mp (hST.trans e.flag.T_normalizes)
  let F := V ⊓ centralizer (R : Set G)
  have hFcard : Nat.card F ≤ 2 := d.component_sylow_fixed_card_le_two S
  have hCR : C ≤ centralizer (R : Set G) := inf_le_right.trans (centralizer_le hRL)
  have hCV : C ≤ normalizer (V : Set G) := (inf_le_left.trans hQT).trans d.flag.T_normalizes
  have hWF : W ≤ F ⊔ C := by
    intro w hw
    have hh : w ∈ (V : Set G) * (C : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left V C hCV]
      exact hsplit.le (hWQ hw)
    obtain ⟨v,hv,c,hc,hvc⟩ := hh
    have hvR : v ∈ centralizer (R : Set G) := by
      have hvw : v = w * c⁻¹ := by rw [←hvc];group
      rw [hvw]
      exact mul_mem (hWR hw) (inv_mem (hCR hc))
    exact hvc ▸ mul_mem_sup (show v ∈ F from ⟨hv,hvR⟩) hc
  have hFC : Disjoint F C := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    exact d.flag.module.fixed_eq_bot.le ⟨hx.1.1,hx.2.2⟩
  have hCF : C ≤ normalizer (F : Set G) :=
    ((inf_le_left.trans d.chosen.core_centralizes).trans (centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcardFC : Nat.card (F ⊔ C : Subgroup G) = Nat.card F * Nat.card C :=
    card_sup_eq_mul_of_normalizes_of_disjoint F C hCF hFC
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes W C
    ((inf_le_left.trans hQT).trans e.flag.T_normalizes)
  have hsize := card_le_of_le (sup_le hWF (show C ≤ F ⊔ C from le_sup_right))
  rw [hcardFC] at hsize
  have hcpos : 0 < Nat.card C := Nat.card_pos
  have hbound : Nat.card W ≤ 2 * Nat.card (W ⊓ C : Subgroup G) := by
    have hh := Nat.mul_le_mul_left (Nat.card (W ⊓ C : Subgroup G)) hsize
    rw [←hprod] at hh
    have hh' := Nat.le_of_mul_le_mul_right (show Nat.card W * Nat.card C ≤
      (Nat.card F * Nat.card (W ⊓ C : Subgroup G)) * Nat.card C from by nlinarith)
    exact (hh' hcpos).trans (Nat.mul_le_mul_right _ hFcard)
  let U := W ⊓ centralizer (L : Set G)
  have heq : W ⊓ C = U := by
    change W ⊓ (Q ⊓ centralizer (L : Set G)) = _
    rw [←inf_assoc,inf_of_le_left hWQ]
  rw [heq,e.module_card] at hbound
  have hUcard : Nat.card U = 8 ∨ Nat.card U = 16 := by
    have hdiv : Nat.card U ∣ 16 := by simpa only [e.module_card] using (card_dvd_of_le (show U ≤ W from inf_le_left))
    have hsize : Nat.card U ≤ 16 := Nat.le_of_dvd (by decide) hdiv
    generalize Nat.card U = n at hdiv hsize hbound ⊢
    have : 8 ≤ n := by omega
    interval_cases n <;> norm_num at hdiv <;> omega
  have hn : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    (le_inf e.flag.T_normalizes (d.normalizes_L.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  rcases hUcard with hc | hc
  · exact ⟨U,inf_le_left,hc,hn,inf_le_right⟩
  · have hUW : U = W := eq_of_le_of_card_ge inf_le_left (by rw [hc,e.module_card])
    exact ⟨W₃,e.third_le,e.third_card,e.third_invariant,
      e.third_le.trans (hUW.ge.trans inf_le_right)⟩
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Subgroup Theory.GroupTheory ChapterC Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- Either single relative block placement forces the original modules not to commute. -/
theorem original_one_block_noncommuting
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hd : Function.Surjective d.localActor)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H)
    (hb : (IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) ∧ IsAlternatingBlock L 5) ∨
      (IsBlock (K.subgroupOf H) ∧ IsAlternatingBlock K 5)) :
    ¬ V ≤ centralizer (W : Set G) := by
  intro hVW
  have hincomp := original_pair_cores_incomparable d hH hd q hq hk
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hPT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [←hjoin]
    exact (e.sylow_centralizer e.normalizes_L).ge.trans inf_le_left
  rcases hb with ⟨hb,ha⟩ | ⟨hb,ha⟩
  · have hm : ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (W : Set G) := by
      intro h
      apply hincomp.2
      rw [←hjoin,←e.sylow_centralizer e.normalizes_L]
      exact le_inf hQT h
    obtain ⟨U,hUW,hUc,hTU,hUL⟩ := one_block_fixed_hyperplane d e hb ha hVW hm
    let e' : Context T K W W₁ W₂ U := {
      hypothesis := e.hypothesis
      chosen := e.chosen
      flag := e.flag
      third_le := hUW
      third_card := hUc
      third_invariant := hTU }
    have hLK : L ≤ normalizer (K : Set G) :=
      (le_centralizer_iff.mp hUL).trans e'.seed_centralizer_knownSimple
    let D := K.pCoreIn 2
    have hDT : D ≤ (T : Subgroup G) := by
      have hh := pCoreIn_mono_of_normalizes (p := 2) (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)
        (sup_le K.le_normalizer e.normalizes_L)
      rw [hjoin] at hh
      exact hh.trans hPT
    have hDne : D ≠ ⊥ := fun h => e.chosen.ne_bot (bot_unique (e.chosen.le_componentCore.trans h.le))
    have hND : normalizer (K : Set G) ≤ normalizer (D : Set G) :=
      normalizer_le_normalizer_characteristic_image K (pCore 2 K)
    have hn := normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
      (T.isPGroup'.to_le hDT) hDne ((sup_le hLK e.normalizes_L).trans hND)
    exact hH.1.2 ((hjoin.ge.trans (sup_le K.le_normalizer e.normalizes_L)).trans (hND.trans hn))
  · have hm : ¬ (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (V : Set G) := by
      rw [hjoin]
      intro h
      apply hincomp.1
      rw [←d.sylow_centralizer d.normalizes_L]
      exact le_inf hPT h
    have hb' : IsBlock (K.subgroupOf (K ⊔ (T : Subgroup G))) := by rwa [hjoin]
    obtain ⟨U,hUV,hUc,hTU,hUK⟩ := one_block_fixed_hyperplane e d hb' ha
      (le_centralizer_iff.mp hVW) hm
    let d' : Context T L V V₁ V₂ U := {
      hypothesis := d.hypothesis
      chosen := d.chosen
      flag := d.flag
      third_le := hUV
      third_card := hUc
      third_invariant := hTU }
    have hKL : K ≤ normalizer (L : Set G) :=
      (le_centralizer_iff.mp hUK).trans d'.seed_centralizer_knownSimple
    exact hH.1.2 (hjoin.ge.trans (sup_le hKL d.normalizes_L))
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
