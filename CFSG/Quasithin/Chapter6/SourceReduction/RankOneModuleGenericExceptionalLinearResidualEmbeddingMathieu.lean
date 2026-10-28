module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualReduction
public import Theory.Mathieu.M23.Properties.MarkedLinearThreeFour
public import Theory.Mathieu.M23.Properties.A5Fixer
public import Theory.Mathieu.M23.Properties.Order
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# Excluding the Mathieu containing component of the exceptional residual

A subgroup of M₂₃ with a PSL₃(4) two-core quotient has trivial two-core:
its core has order at most two, and a nontrivial core would put a subgroup
of order divisible by five in an involution centralizer. For an actual
normal component with M₂₃ quotient, its conjugation action therefore gives
a faithful PSL₃(4) image. Sylow conjugacy aligns the unipotent subgroup;
the checked Mathieu marking theorem excludes the original diagram actor.

All quotient markings and conjugation actions are transported explicitly.
The final export applies to the literal embedded residual of H*. It
settles the M₂₃ containing row; it does not settle maximality or the other
containing rows.

Source: Aschbacher–Smith, 5.1.12 and the opening of 5.1.14, printed
pp.635 and 638 (refs/quasithin.pdf); the Mathieu marking uses the actual
ATLAS permutation carrier and its existing checked local geometry.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.MinimalParabolicWitness
open Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric

private theorem psl_card_four {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) : Nat.card PSL(3,F) = 20160 := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let e : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, Matrix.PSL3Four.card_F])
  exact (Nat.card_congr (Atlas.fieldEquivPSL 3 e).toEquiv).trans Matrix.PSL3Four.card_PSL

/-- A subgroup of M23 with PSL3(4) two-core quotient has trivial two-core. -/
theorem mathieu23_linear_four_core_eq_bot (B : Subgroup M23)
    (hq : Nat.card (B ⧸ pCore 2 B) = 20160) : pCore 2 B = ⊥ := by
  have hd := B.card_subgroup_dvd_card
  rw [m23_order, ← (pCore 2 B).card_mul_index,
    show (pCore 2 B).index = 20160 from hq] at hd
  have hd' : Nat.card (pCore 2 B) ∣ 2 * 253 :=
    (Nat.mul_dvd_mul_iff_right (by decide : 0 < 20160)).mp hd
  have hc : Nat.Coprime (Nat.card (pCore 2 B)) 253 := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 253).pow_left n
  have hdiv : Nat.card (pCore 2 B) ∣ 2 := hc.dvd_of_dvd_mul_right hd'
  by_contra hne
  have hcard : Nat.card (pCore 2 B) = 2 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hdiv).resolve_left
      (fun h1 => hne ((pCore 2 B).eq_bot_iff_card.mpr h1))
  let U := (pCore 2 B).map B.subtype
  have hU : Nat.card U = 2 := (card_map_of_injective B.subtype_injective).trans hcard
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hzG : orderOf (z : M23) = 2 := (orderOf_coe z).trans hz
  have heq : zpowers (z : M23) = U := eq_of_le_of_card_ge
    (zpowers_le.mpr z.property) (by rw [Nat.card_zpowers,hzG,hU])
  have hBN : B ≤ normalizer (U : Set M23) :=
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  rw [← heq, normalizer_zpowers_eq_centralizer_of_order_two _ hzG] at hBN
  have h5 : 5 ∣ Nat.card B :=
    (by decide : 5 ∣ 20160).trans (hq ▸ card_quotient_dvd_card (pCore 2 B))
  exact m23_involution_centralizer_not_five z hzG (h5.trans (card_dvd_of_le hBN))

/-- A literal Mathieu quotient with a two-group kernel on the normalized
subgroup excludes the graph actor. The ambient map need not be injective. -/
theorem no_linear_four_graph_of_mathieu23_map
    {Y : Type*} [Group Y] [Finite Y] (S : Sylow 2 Y) (K : Subgroup Y)
    (hn : (S : Subgroup Y) ≤ normalizer (K : Set Y))
    (f : Y →* M23) (hk : IsPGroup 2 (f.subgroupMap K).ker) :
    ¬ HasLinearFourGraphAction (S : Subgroup Y) K := by
  rintro ⟨F,hF,hfin,hcard,e,t,ht,a,b,ha,hb,hd⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hcard)
  let B := K.map f
  let j := MonoidHom.quotientPCoreEquivOfSurjective (f.subgroupMap K)
    (f.subgroupMap_surjective K) hk
  have hB : pCore 2 B = ⊥ := mathieu23_linear_four_core_eq_bot B
    ((Nat.card_congr j.symm.toEquiv).trans
      ((Nat.card_congr e.toEquiv).trans (psl_card_four hcard)))
  let j' : (K ⧸ pCore 2 K) ≃* B := j.trans
    ((QuotientGroup.quotientMulEquivOfEq hB).trans QuotientGroup.quotientBot)
  have hj (k : K) : (j' (QuotientGroup.mk' (pCore 2 K) k) : M23) = f k := by
    change (((QuotientGroup.quotientMulEquivOfEq hB).trans QuotientGroup.quotientBot)
      (j (QuotientGroup.mk' (pCore 2 K) k)) : M23) = f k
    rw [MonoidHom.quotientPCoreEquivOfSurjective_mk]
    rfl
  let v := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hv : Function.Surjective v := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨R,hR⟩ := NormalSylowQuotientAction.intersection_sylow S K hn
  let Q := R.mapSurjective hv
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) Q
    (unipotentSylow F (n := 2) (by decide) hcard)
  let c := MulAut.conj g
  let e' := e.trans c
  let i : PSL(3,F) →* M23 := B.subtype.comp (j'.toMonoidHom.comp e'.symm.toMonoidHom)
  have hi : Function.Injective i := B.subtype_injective.comp (j'.injective.comp e'.symm.injective)
  have hiv (k : K) : i (e' (QuotientGroup.mk' (pCore 2 K) k)) = f k := by
    change (j' (e'.symm (e' (QuotientGroup.mk' _ k))) : M23) = _
    rw [e'.symm_apply_apply]
    exact hj k
  have hu : ((R : Subgroup K).map v).map c.toMonoidHom = unipotent F := by
    exact congrArg Sylow.toSubgroup hg
  obtain ⟨P,hP⟩ := (S.isPGroup'.map f).exists_le_sylow
  have hPi : (unipotent F).map i ≤ (P : Subgroup M23) := by
    rw [← hu]
    rintro _ ⟨_,⟨_,⟨k,hk,rfl⟩,rfl⟩,rfl⟩
    change i (e' (QuotientGroup.mk' _ k)) ∈ (P : Subgroup M23)
    rw [hiv]
    apply hP
    apply mem_map_of_mem f
    change k ∈ (S : Subgroup Y).subgroupOf K
    rwa [← hR]
  let b' := MulAut.congr c b
  have hact : ∀ x, i (b' x) = f t * i x * (f t)⁻¹ := by
    intro x
    obtain ⟨k,hkx⟩ := (c.surjective.comp hv) x
    change e' (QuotientGroup.mk' _ k) = x at hkx
    rw [← hkx]
    have hbe : b' (e' (QuotientGroup.mk' _ k)) = e' (QuotientGroup.mk' _ (a k)) := by
      change c (b (c.symm (c (e (QuotientGroup.mk' _ k))))) = _
      rw [c.symm_apply_apply, ← hb]
      rfl
    rw [hbe,hiv,hiv,ha]
    simp only [map_mul,map_inv]
  have hbU : (unipotent F).map b'.toMonoidHom = unipotent F := by
    apply eq_of_le_of_card_ge
    · rw [← hu]
      rintro _ ⟨_,⟨_,⟨k,hk,rfl⟩,rfl⟩,rfl⟩
      have hak : a k ∈ (R : Subgroup K) := by
        rw [hR]
        change (a k : Y) ∈ (S : Subgroup Y)
        rw [ha]
        have hkS : k ∈ (S : Subgroup Y).subgroupOf K := hR ▸ hk
        exact (S : Subgroup Y).mul_mem ((S : Subgroup Y).mul_mem ht hkS)
          ((S : Subgroup Y).inv_mem ht)
      refine ⟨v (a k),mem_map_of_mem v hak,?_⟩
      change c (e (QuotientGroup.mk' _ (a k))) = c (b (c.symm (c (e (QuotientGroup.mk' _ k)))))
      rw [c.symm_apply_apply,hb]
    · rw [card_map_of_injective b'.injective]
  have hz := m23_no_marked_linear_three_four_graph hcard i hi P hPi (f t)
    (hP (mem_map_of_mem f ht)) b' hbU hact
  have hb' : b' = c * b * c⁻¹ := by
    ext x
    rfl
  rw [hb',map_mul,map_mul,map_inv] at hz
  have hz' : diagramAction F (n := 2) (by decide) hcard b = 1 := by
    have hh := congrArg (fun x : Equiv.Perm Bool =>
      (diagramAction F (n := 2) (by decide) hcard c)⁻¹ * x *
        (diagramAction F (n := 2) (by decide) hcard c)) hz
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one,
      one_mul] using hh
  apply hd
  rw [← diagramAction_ker F (n := 2) (by decide) hcard]
  exact hz'

/-- Conjugation on a normal M23 quotient is realized by an actual homomorphism
into M23; on the original component this is the given quotient marking. -/
theorem exists_mathieu23_map_of_normal_quotient
    {Y : Type*} [Group Y] [Finite Y] (C : Subgroup Y) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* M23) :
    ∃ f : Y →* M23, ∀ c : C, f c = e (QuotientGroup.mk' (pCore 2 C) c) := by
  let j : M23 ≃* MulAut M23 := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot M23Geometry.m23_center_eq_bot,
      m23_conj_surjective⟩
  let f : Y →* M23 := j.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (normalQuotientAction C (pCore 2 C)))
  refine ⟨f, ?_⟩
  intro c
  apply j.injective
  change j (j.symm (MulAut.congr e (normalQuotientAction C (pCore 2 C) c))) = _
  rw [j.apply_symm_apply, normalQuotientAction_inner]
  change MulAut.congr e (MulAut.conj (QuotientGroup.mk' _ c)) =
    MulAut.conj (e (QuotientGroup.mk' _ c))
  ext x : 1
  change e (QuotientGroup.mk' _ c * e.symm x * (QuotientGroup.mk' _ c)⁻¹) = _
  simp only [map_mul, map_inv, e.apply_symm_apply, MulAut.conj_apply]

/-- A graph actor cannot occur inside an actual normal containing component
whose intrinsic two-core quotient is M23. -/
theorem no_linear_four_graph_of_normal_mathieu23_quotient
    {Y : Type*} [Group Y] [Finite Y] (S : Sylow 2 Y) (K C : Subgroup Y)
    [C.Normal] (hn : (S : Subgroup Y) ≤ normalizer (K : Set Y))
    (hKC : K ≤ C) (e : (C ⧸ pCore 2 C) ≃* M23) :
    ¬ HasLinearFourGraphAction (S : Subgroup Y) K := by
  obtain ⟨f,hf⟩ := exists_mathieu23_map_of_normal_quotient C e
  apply no_linear_four_graph_of_mathieu23_map S K hn f
  have hk : (f.subgroupMap K).ker ≤ (pCore 2 C).comap (inclusion hKC) := by
    intro k hk
    have hfk : f (k : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
    change f ((inclusion hKC k : C) : Y) = 1 at hfk
    rw [hf (inclusion hKC k)] at hfk
    change inclusion hKC k ∈ pCore 2 C
    apply (QuotientGroup.eq_one_iff _).mp
    exact e.injective (hfk.trans (map_one e).symm)
  exact (pCore_isPGroup.comap_of_injective (inclusion hKC)
    (inclusion_injective hKC)).to_le hk

/-- Restriction to an actual common overgroup preserves the specified diagram
actor and its quotient marking. -/
theorem HasLinearFourGraphAction.subgroupOf
    {G : Type*} [Group G] {S K Y : Subgroup G}
    (h : HasLinearFourGraphAction S K) (hSY : S ≤ Y) (hKY : K ≤ Y) :
    HasLinearFourGraphAction (S.subgroupOf Y) (K.subgroupOf Y) := by
  obtain ⟨F,hF,hfin,hcard,e,t,ht,a,b,ha,hb,hd⟩ := h
  let i : K.subgroupOf Y ≃* K := subgroupOfEquivOfLe hKY
  let j := QuotientGroup.congr _ _ i (pCore_map_iso 2 i)
  refine ⟨F,hF,hfin,hcard,j.trans e,⟨t,hSY ht⟩,ht,MulAut.congr i.symm a,b,?_,?_,hd⟩
  · intro k
    apply Subtype.ext
    change (i (i.symm (a (i k))) : G) = t * (i k : G) * t⁻¹
    rw [i.apply_symm_apply]
    exact ha (i k)
  · intro k
    change e (j (QuotientGroup.mk' _ (i.symm (a (i k))))) =
      b (e (j (QuotientGroup.mk' _ k)))
    change e (QuotientGroup.mk' _ (i (i.symm (a (i k))))) =
      b (e (QuotientGroup.mk' _ (i k)))
    rw [i.apply_symm_apply]
    exact hb (i k)

/-- The M23 branch of the proper-containing-component exclusion, on the
literal relative component C in Y. -/
theorem linear_four_graph_excludes_mathieu23_container
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {K Y : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hg : HasLinearFourGraphAction (T : Subgroup G) K)
    (C : Subgroup Y) [C.Normal] (hKC : K ≤ C.map Y.subtype) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* M23) := by
  rintro ⟨e⟩
  have hKY : K ≤ Y := hKC.trans (map_subtype_le C)
  have hK'C : K.subgroupOf Y ≤ C := by
    intro k hk
    obtain ⟨c,hc,he⟩ := hKC hk
    exact Y.subtype_injective he ▸ hc
  apply no_linear_four_graph_of_normal_mathieu23_quotient
    (T.subtype hTY) (K.subgroupOf Y) C ?_ hK'C e
  · exact hg.subgroupOf hTY hKY
  · intro t ht
    apply mem_normalizer_iff.mpr
    intro k
    exact mem_normalizer_iff.mp (hn ht) (k : G)

/-- Apply the genuine graph actor of the original H-star residual to every
actual normal containing component with M23 two-core quotient. -/
theorem linear_residual_excludes_mathieu23_container
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {M H Y : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hHY : H ≤ Y) (C : Subgroup Y) [C.Normal]
    (hRC : residual H ≤ C.map Y.subtype) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* M23) :=
  linear_four_graph_excludes_mathieu23_container T (hH.1.1.2.trans hHY)
    (hH.1.1.2.trans (le_normalizer_residual H))
    (linear_residual_graph_action T hTM hH hlinear) C hRC

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
