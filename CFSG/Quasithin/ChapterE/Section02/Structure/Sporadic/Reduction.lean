module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.IntrinsicParabolics
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.SolvableOuterQuotient
/-!
# Normal sporadic minimal-parabolic reduction

The original core-free minimal parabolic acts faithfully on its simple normal
supplement. Proper generating Sylow overgroups contradict its unique maximal
overgroup. These reductions preserve the original quotient and its Sylow.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.Sporadic
variable {G M : Type*} [Group G] [Finite G] [Group M]

theorem not_minimal_of_pair (T : Sylow 2 G) (P Q : Subgroup G)
    (hp : P ≠ ⊤) (hq : Q ≠ ⊤) (htp : (T : Subgroup G) ≤ P)
    (htq : (T : Subgroup G) ≤ Q) (hjoin : P ⊔ Q = ⊤) :
    ¬ ChapterB.IsMinimalParabolicOver T ⊤ :=
  ChapterB.not_minimalParabolic_of_two_overgroups T ⊤ P Q (by simp) hjoin hp hq
    (htp.trans P.le_normalizer) (htq.trans Q.le_normalizer)
    (by simpa using htp) (by simpa using htq)

theorem not_minimal_of_model (T : Sylow 2 G) (e : G ≃* M)
    (hm : ∀ S : Sylow 2 M, ¬ ChapterB.IsMinimalParabolicOver S ⊤) :
    ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  intro h
  exact hm _ (ChapterB.minimalParabolic_surjective_core T h e.toMonoidHom e.surjective
    (by rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]; exact bot_le))

theorem faithful_normal_structure (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hcore : ChapterB.minimalParabolicCore T hP = ⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (ha : ¬ IsMulCommutative L)
    (hgen : L ⊔ (T : Subgroup G) = ⊤) :
    generalizedFitting G = L ∧ centralizer (L : Set G) = ⊥ := by
  have hc : pCore 2 G = ⊥ := le_bot_iff.mp
    ((ChapterB.minimalParabolicTwoCore_le_core T hP).trans hcore.le)
  have hq : IsPGroup 2 (G ⧸ L) := by
    have hm : (T : Subgroup G).map (QuotientGroup.mk' L) = ⊤ := by
      have he := congrArg (Subgroup.map (QuotientGroup.mk' L)) hgen
      simpa only [Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective L)] using he
    have h := T.isPGroup'.map (QuotientGroup.mk' L)
    rw [hm] at h
    exact h.of_equiv topEquiv
  exact (simple_two_quotient_structure L ha hq hc).imp_right And.left

omit [Finite G] in
theorem normal_eq_top_of_inner (L : Subgroup G) [L.Normal]
    (hc : centralizer (L : Set G) = ⊥) (e : L ≃* M)
    (hi : Function.Surjective (MulAut.conj : M →* MulAut M)) : L = ⊤ := by
  have hs : Function.Surjective (MulAut.conj : L →* MulAut L) := by
    intro a
    obtain ⟨x,hx⟩ := hi ((MulAut.congr e) a)
    refine ⟨e.symm x,(MulAut.congr e).injective ?_⟩
    rw [MulAut.congr_conj,e.apply_symm_apply,hx]
  have hinner : MulAut.innerSubgroup L = ⊤ := MonoidHom.range_eq_top.mpr hs
  have h := MulAut.conjNormal_comap_innerSubgroup L
  rw [hinner,comap_top,hc,sup_bot_eq] at h
  exact h.symm

omit [Finite G] in
theorem not_solvable_of_normal_simple (L : Subgroup G) [IsSimpleGroup L]
    (ha : ¬ IsMulCommutative L) : ¬ Group.IsSolvable G := by
  let : Group.IsPerfect L := ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (_root_.commutator L) inferInstance).resolve_left (fun h => ha ((commutator_eq_bot_iff L).mp h))⟩
  intro h
  let := h
  exact Group.IsPerfect.not_isSolvable L inferInstance

omit [Finite G] in
theorem proper_of_solvable (hn : ¬ Group.IsSolvable G) (P : Subgroup G)
    [Group.IsSolvable P] : P ≠ ⊤ := by
  intro he
  let e : P ≃* G := (MulEquiv.subgroupCongr he).trans topEquiv
  exact hn (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

omit [Finite G] in
theorem proper_of_core_centralizer [Nontrivial G] (hc : pCore 2 G = ⊥)
    (P : Subgroup G) (hP : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) : P ≠ ⊤ := by
  intro he
  subst P
  have hz : pCore 2 (⊤ : Subgroup G) = ⊥ := by
    apply Subgroup.map_injective (f := (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom) topEquiv.injective
    rw [pCore_map_iso 2 topEquiv, hc, Subgroup.map_bot]
  rw [hz] at hP
  have ht : (⊤ : Subgroup (⊤ : Subgroup G)) ≤ ⊥ := by
    intro x _
    apply hP
    intro y hy
    have hy : y = 1 := mem_bot.mp hy
    rw [hy]
    simp
  exact top_ne_bot (le_bot_iff.mp ht)

theorem core_eq_bot_of_simple [IsSimpleGroup G] (ha : ¬ IsMulCommutative G) :
    pCore 2 G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 2 G) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 2 G := (h ▸ (pCore_isPGroup (p := 2) (G := G))).of_equiv topEquiv
    let : Group.IsNilpotent G := hp.isNilpotent
    let : Group.IsPerfect G := ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (_root_.commutator G) inferInstance).resolve_left (fun h => ha ((commutator_eq_bot_iff G).mp h))⟩
    exact (Group.IsPerfect.not_isSolvable G inferInstance).elim


theorem not_minimal_of_marked_pair [Finite M] (T : Sylow 2 G) (e : G ≃* M)
    (S : Sylow 2 M) (P Q : Subgroup M) (hp : P ≠ ⊤) (hq : Q ≠ ⊤)
    (hsp : (S : Subgroup M) ≤ P) (hsq : (S : Subgroup M) ≤ Q)
    (hjoin : P ⊔ Q = ⊤) : ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  apply not_minimal_of_model T e
  intro R hr
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M R S
  have hm := ChapterB.minimalParabolic_surjective_core R hr
    (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective
    (by rw [(MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj g).injective]; exact bot_le)
  have he : R.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective = S := hg
  rw [he] at hm
  exact not_minimal_of_pair S P Q hp hq hsp hsq hjoin hm

omit [Finite G] in
theorem noncomm_of_equiv (L : Subgroup G) (ha : ¬ IsMulCommutative L)
    (e : L ≃* M) : ¬ IsMulCommutative M := by
  intro hm
  let := hm
  exact ha (IsMulCommutative.of_comm fun x y => e.injective (by simpa only [map_mul] using mul_comm' (e x) (e y)))

omit [Finite G] in
theorem proper_of_core_quotient [Finite M] (hc : pCore 2 G = ⊥)
    (P : Subgroup G) (e : (P ⧸ pCore 2 P) ≃* M)
    (hsize : Nat.card M < Nat.card G) : P ≠ ⊤ := by
  intro he
  subst P
  have hz : pCore 2 (⊤ : Subgroup G) = ⊥ := by
    apply Subgroup.map_injective (f := (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom) topEquiv.injective
    rw [pCore_map_iso 2 topEquiv, hc, Subgroup.map_bot]
  let d : ((⊤ : Subgroup G) ⧸ pCore 2 (⊤ : Subgroup G)) ≃* G :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans topEquiv
  exact (ne_of_lt hsize) ((Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr d.toEquiv))

end CFSG.Quasithin.ChapterE.Structure.Sporadic
