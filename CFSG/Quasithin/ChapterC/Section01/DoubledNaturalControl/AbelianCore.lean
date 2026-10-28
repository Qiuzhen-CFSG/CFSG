module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head
public import Theory.GroupTheory.CentralizerIndexBound

/-!
# The abelian-core branch of doubled-natural control

Let N be an abelian normal subgroup of a finite group J with a specified
simple quotient J/N. Suppose N is contained in R, the quotient image of R
has order at most four, and a normal subgroup U of N has displacement index
four under every element of R outside N. If [N,J] is not contained in U,
simplicity forces every such element to have displacement index greater
than four on N. Every abelian subgroup of R outside N then has smaller
order than N. Thus N is the unique abelian subgroup of maximum order in R,
so is characteristic in R, contradicting the genuine MS3 condition.

The resulting containment gives [N,L]=U when [U,L]=U. The binary MS adapter
retains the intrinsic two-core and all subtype maps. The parent supplies
abelianness of the core, simplicity of the actual quotient, the image bound,
and the fixed indices from the compatible doubled-natural action. This
module does not prove the nonabelian-core case or the full MS classification.

Source context: Aschbacher--Smith, combined manuscript (1 March 2004),
C.1.31(MS3), printed p.135, and the doubled-natural branch of C.1.37,
printed pp.142--143. This is a separate sufficient abelian-core argument.
-/

public section

namespace CFSG.Quasithin.ChapterC.DoubledNaturalControl.AbelianCore
open Subgroup
open scoped commutatorElement IsMulCommutative

variable {G H : Type*} [Group G] [Group H]

private def displacement (M : Subgroup G) [M.Normal] [IsMulCommutative M]
    (r : G) : M →* G where
  toFun m := ⁅(m : G), r⁆
  map_one' := by simp
  map_mul' x y := by
    change ⁅(x : G) * (y : G), r⁆ = ⁅(x : G), r⁆ * ⁅(y : G), r⁆
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hx : ⁅(x : G), r⁆ ∈ M :=
      commutator_le_left M (zpowers r)
        (commutator_mem_commutator x.property (mem_zpowers r))
    have hy : ⁅(y : G), r⁆ ∈ M :=
      commutator_le_left M (zpowers r)
        (commutator_mem_commutator y.property (mem_zpowers r))
    have hC : M ≤ centralizer (M : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    rw [(hC x.property _ hy).symm, mul_inv_cancel_right,
      (hC hy _ hx).symm]

private theorem displacement_ker (M : Subgroup G) [M.Normal]
    [IsMulCommutative M] (r : G) :
    (displacement M r).ker = (centralizer ({r} : Set G)).subgroupOf M := by
  ext m
  change ⁅(m : G), r⁆ = 1 ↔ (m : G) ∈ centralizer ({r} : Set G)
  rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff]

private theorem displacement_range_card (M : Subgroup G) [M.Normal]
    [IsMulCommutative M] (r : G) :
    Nat.card (displacement M r).range = (centralizer ({r} : Set G)).relIndex M := by
  rw [← index_ker, displacement_ker]
  rfl

private theorem displacement_range_le (M : Subgroup G) [M.Normal]
    [IsMulCommutative M] (r : G) : (displacement M r).range ≤ M := by
  rintro x ⟨m, rfl⟩
  exact commutator_le_left M (zpowers r)
    (commutator_mem_commutator m.property (mem_zpowers r))

private theorem quotient_centralizer_eq_top [IsSimpleGroup H]
    (N U : Subgroup G) [N.Normal] [U.Normal] [IsMulCommutative N]
    (q : G →* H) (hq : Function.Surjective q) (hker : q.ker = N)
    (r : G) (hr : r ∉ N) (hcomm : ∀ n ∈ N, ⁅n,r⁆ ∈ U) :
    ⁅N, (⊤ : Subgroup G)⁆ ≤ U := by
  let p := QuotientGroup.mk' U
  let K := (centralizer (N.map p : Set (G ⧸ U))).comap p
  let : K.Normal := inferInstance
  have hNK : N ≤ K := by
    intro n hn
    change p n ∈ centralizer (N.map p : Set (G ⧸ U))
    rintro x ⟨m, hm, rfl⟩
    have hC : N ≤ centralizer (N : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    simpa only [map_mul] using congrArg p (hC hn m hm)
  have hrK : r ∈ K := by
    change p r ∈ centralizer (N.map p : Set (G ⧸ U))
    apply mem_centralizer_iff_commutator_eq_one.mpr
    rintro x ⟨n, hn, rfl⟩
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hcomm n hn)
  have hnormal : (K.map q).Normal :=
    (inferInstance : K.Normal).map q hq
  have htop : K.map q = ⊤ := by
    rcases hnormal.eq_bot_or_eq_top with hz | ht
    · have hKN : K ≤ N := by
        rw [← hker]
        exact (map_eq_bot_iff K).mp hz
      exact (hr (hKN hrK)).elim
    · exact ht
  have hK : K = ⊤ := by
    have ht := congrArg (fun B : Subgroup H => B.comap q) htop
    simpa only [comap_map_eq, hker, sup_eq_left.mpr hNK, comap_top] using ht
  apply commutator_le.mpr
  intro n hn x _
  have hx : x ∈ K := hK ▸ mem_top x
  have hc := mem_centralizer_iff_commutator_eq_one.mp hx
    (p n) (mem_map_of_mem p hn)
  apply (QuotientGroup.eq_one_iff _).mp
  change p ⁅n,x⁆ = 1
  rw [map_commutatorElement]
  exact hc

private theorem displacement_gt_four [Finite G] [IsSimpleGroup H]
    (N U : Subgroup G) [N.Normal] [U.Normal] [IsMulCommutative N]
    (hUN : U ≤ N) (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = N) (hnot : ¬ ⁅N, (⊤ : Subgroup G)⁆ ≤ U)
    (r : G) (hr : r ∉ N)
    (hfour : (centralizer ({r} : Set G)).relIndex U = 4) :
    4 < (centralizer ({r} : Set G)).relIndex N := by
  let : IsMulCommutative U := le_centralizer_iff_isMulCommutative.mp
    (hUN.trans ((le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative N)).trans (centralizer_le hUN)))
  by_contra hlarge
  have hsmall := Nat.le_of_not_gt hlarge
  have hle : (displacement U r).range ≤ (displacement N r).range := by
    rintro x ⟨u, rfl⟩
    exact ⟨⟨u, hUN u.property⟩, rfl⟩
  have heq : (displacement U r).range = (displacement N r).range :=
    eq_of_le_of_card_ge hle (by
      rw [displacement_range_card, displacement_range_card, hfour]
      exact hsmall)
  have hrange : (displacement N r).range ≤ U :=
    heq ▸ displacement_range_le U r
  apply hnot
  apply quotient_centralizer_eq_top N U q hq hker r hr
  intro n hn
  exact hrange ⟨⟨n, hn⟩, rfl⟩

/-- With an abelian normal core, a simple quotient, quotient radical of order
at most four, and doubled-natural displacement four, MS3 forces all core
commutators into U. The displacement and image bounds are literal inputs. -/
theorem commutator_le [Finite G] [IsSimpleGroup H]
    (N U R : Subgroup G) [N.Normal] [U.Normal] [IsMulCommutative N]
    (hUN : U ≤ N) (hUne : U ≠ ⊥) (hNR : N ≤ R)
    (q : G →* H) (hq : Function.Surjective q) (hker : q.ker = N)
    (hRcard : Nat.card (R.map q) ≤ 4)
    (hdisp : ∀ r ∈ R, r ∉ N → (centralizer ({r} : Set G)).relIndex U = 4)
    (hMS3 : MSCharacteristicCondition R) : ⁅N, (⊤ : Subgroup G)⁆ ≤ U := by
  let : Finite H := Finite.of_surjective q hq
  by_contra hnot
  have hlarge (r : G) (hrR : r ∈ R) (hrN : r ∉ N) :
      4 < (centralizer ({r} : Set G)).relIndex N :=
    displacement_gt_four N U hUN q hq hker hnot r hrN (hdisp r hrR hrN)
  have hstrict (B : Subgroup G) (hBR : B ≤ R) (hB : IsMulCommutative B)
      (hBN : ¬ B ≤ N) : Nat.card B < Nat.card N := by
    obtain ⟨r, hrB, hrN⟩ := SetLike.not_le_iff_exists.mp hBN
    have hBC : B ≤ centralizer ({r} : Set G) := by
      intro b hb
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hB.is_comm.comm (⟨b,hb⟩ : B) ⟨r,hrB⟩))
    have hcount := card_le_centralizer_card_mul_relIndex B N {r} hBC
    have himage : N.relIndex B ≤ 4 := by
      rw [← hker, relIndex_ker]
      exact (card_le_of_le (map_mono hBR)).trans hRcard
    have hcard := index_mul_card ((centralizer ({r} : Set G)).subgroupOf N)
    change (centralizer ({r} : Set G)).relIndex N *
      Nat.card ((centralizer ({r} : Set G)).subgroupOf N) = Nat.card N at hcard
    calc
      Nat.card B ≤ Nat.card ((centralizer ({r} : Set G)).subgroupOf N) *
          N.relIndex B := hcount
      _ ≤ Nat.card ((centralizer ({r} : Set G)).subgroupOf N) * 4 :=
        Nat.mul_le_mul_left _ himage
      _ < Nat.card ((centralizer ({r} : Set G)).subgroupOf N) *
          (centralizer ({r} : Set G)).relIndex N :=
        Nat.mul_lt_mul_of_pos_left (hlarge r (hBR hrB) hrN) Nat.card_pos
      _ = Nat.card N := (Nat.mul_comm _ _).trans hcard
  let C := N.subgroupOf R
  have hchar : C.Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro a
    let B := (C.map a.toMonoidHom).map R.subtype
    have hBR : B ≤ R := map_subtype_le _
    have hB : IsMulCommutative B := inferInstance
    have hcard : Nat.card B = Nat.card N := by
      change Nat.card ((C.map a.toMonoidHom).map R.subtype) = Nat.card N
      rw [card_map_of_injective R.subtype_injective,
        card_map_of_injective a.injective]
      exact Nat.card_congr (subgroupOfEquivOfLe hNR).toEquiv
    have hBN : B ≤ N := by
      by_contra hh
      exact (Nat.lt_irrefl (Nat.card N)) (hcard ▸ hstrict B hBR hB hh)
    intro x hx
    exact hBN (mem_map_of_mem R.subtype hx)
  have hCne : C ≠ ⊥ := by
    intro hbot
    have hNbot : N = ⊥ := by
      have hm := congrArg (fun B : Subgroup R => B.map R.subtype) hbot
      simpa only [C, map_subgroupOf_eq_of_le hNR, Subgroup.map_bot] using hm
    exact hUne (le_bot_iff.mp (hNbot ▸ hUN))
  have hCnormal : (C.map R.subtype).Normal := by
    dsimp only [C]
    rw [map_subgroupOf_eq_of_le hNR]
    infer_instance
  exact hMS3 C hchar hCne hCnormal

/-- The source equality follows as soon as U is generated by its commutators
with L. No exponent bound on N is required. -/
theorem commutator_eq [Finite G] [IsSimpleGroup H]
    (N U R L : Subgroup G) [N.Normal] [U.Normal] [IsMulCommutative N]
    (hUN : U ≤ N) (hUne : U ≠ ⊥) (hNR : N ≤ R)
    (q : G →* H) (hq : Function.Surjective q) (hker : q.ker = N)
    (hRcard : Nat.card (R.map q) ≤ 4)
    (hdisp : ∀ r ∈ R, r ∉ N → (centralizer ({r} : Set G)).relIndex U = 4)
    (hMS3 : MSCharacteristicCondition R) (hUL : ⁅U,L⁆ = U) : ⁅N,L⁆ = U := by
  apply le_antisymm
  · exact (commutator_mono le_rfl le_top).trans
      (commutator_le N U R hUN hUne hNR q hq hker hRcard hdisp hMS3)
  · rw [← hUL]
    exact commutator_mono hUN le_rfl

end CFSG.Quasithin.ChapterC.DoubledNaturalControl.AbelianCore

namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}}
  {L R : Subgroup J}

/-- The abelian-core specialization of the actual binary MS input. The parent
supplies the simple quotient, radical image bound and doubled-natural
per-element fixed indices from its compatible action. -/
theorem Input.commutatorCore_eq_of_abelian
    (h : Input κ L R) (U : Subgroup J) [U.Normal]
    [IsMulCommutative (pCore 2 J)] [IsSimpleGroup (J ⧸ pCore 2 J)]
    (hUN : U ≤ pCore 2 J) (hUne : U ≠ ⊥) (hUL : ⁅U,L⁆ = U)
    (hRcard : Nat.card (R.map (QuotientGroup.mk' (pCore 2 J))) ≤ 4)
    (hdisp : ∀ r ∈ R, r ∉ pCore 2 J →
      (centralizer ({r} : Set J)).relIndex U = 4) :
    commutatorCore L = U ∧ (⁅pCore 2 L, (⊤ : Subgroup L)⁆).map L.subtype = U := by
  have heq : commutatorCore L = U :=
    DoubledNaturalControl.AbelianCore.commutator_eq (pCore 2 J) U R L
      hUN hUne h.radical.twoCore_le (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      hRcard hdisp h.characteristic hUL
  exact ⟨heq, h.commutatorCore_eq_internal.symm.trans heq⟩

end CFSG.Quasithin.ChapterC.BinaryMS
