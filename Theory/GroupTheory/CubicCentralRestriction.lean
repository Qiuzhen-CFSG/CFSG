module

public import Theory.GroupTheory.CentralCoprimeAbelianLift
public import Theory.GroupTheory.SolvableResidual.Transport

/-!
# Residuals of cubic central extensions with abelian two-kernels

Let X → H have central kernel of order three, contained in X′. Suppose
H → S has abelian two-group kernel, S is perfect and O₂(S)=1. Lift the
two-kernel to a normal two-subgroup Q of X by coprime central lifting.
The kernel of X/Q → S is still cubic and central. Its inclusion in the
derived group makes X/Q perfect. The solvable residual of X surjects
onto X/Q; its kernel is exactly its two-core. The resulting central cover
of S keeps the prescribed projection on every residual representative.

This is the intrinsic restriction argument used for the hexad in
Aschbacher--Smith 13.8.21(2), printed p.956. The inclusion in X′ is an
explicit input, supplied there by transfer from the perfect ambient cover.
-/

namespace CubicCentralRestriction

open Subgroup
open scoped IsMulCommutative

private theorem splitting {X H S : Type*} [Group X] [Finite X] [Group H] [Group S]
    [Group.IsPerfect S]
    (f : X →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center X) (hcard : Nat.card f.ker = 3)
    (hderived : f.ker ≤ commutator X)
    (r : H →* S) (hr : Function.Surjective r)
    [IsMulCommutative r.ker] (hR : IsPGroup 2 r.ker) :
    ∃ (Q : Subgroup X) (hQ : Q.Normal),
      letI := hQ
      IsPGroup 2 Q ∧
      ∃ s : X ⧸ Q →* S, Function.Surjective s ∧
        s.comp (QuotientGroup.mk' Q) = r.comp f ∧
        s.ker ≤ center (X ⧸ Q) ∧ Nat.card s.ker = 3 ∧
        Group.IsPerfect (X ⧸ Q) := by
  have hcop : Nat.Coprime 2 (Nat.card f.ker) := by rw [hcard]; decide
  obtain ⟨Q, hQp, _, hQmap, hQnorm⟩ :=
    exists_abelian_prime_lift_of_central_coprime_kernel f hf hcentral hcop r.ker hR
  have hQnormal : Q.Normal := normalizer_eq_top_iff.mp (top_unique (by
    simpa only [r.ker.normalizer_eq_top, comap_top] using hQnorm))
  let := hQnormal
  have hker : (r.comp f).ker = Q ⊔ f.ker := by
    rw [← MonoidHom.comap_ker, ← hQmap, comap_map_eq]
  have hQker : Q ≤ (r.comp f).ker := hker ▸ le_sup_left
  let q := QuotientGroup.mk' Q
  let s := QuotientGroup.lift Q (r.comp f) hQker
  have hs : Function.Surjective s :=
    QuotientGroup.lift_surjective_of_surjective Q (r.comp f) (hr.comp hf) hQker
  have hsKer : s.ker = f.ker.map q := by
    rw [QuotientGroup.ker_lift, hker, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hscenter : s.ker ≤ center (X ⧸ Q) := by
    rw [hsKer]
    rintro x ⟨z, hz, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Q y
    exact (map_mul q y z).symm.trans ((congrArg q
      (mem_center_iff.mp (hcentral hz) y)).trans (map_mul q z y))
  have hdis : Disjoint Q f.ker := by
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hn]; exact hcop.pow_left n)
  have hinj : Function.Injective (q.subgroupMap f.ker) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxQ : (x : X) ∈ Q := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
    exact Subtype.ext (hdis.le_bot ⟨hxQ, x.property⟩)
  have hscard : Nat.card s.ker = 3 := by
    rw [hsKer, ← Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap f.ker)
      ⟨hinj, q.subgroupMap_surjective _⟩).toEquiv, hcard]
  have hdermap : (commutator X).map q = commutator (X ⧸ Q) := by
    rw [map_commutator_eq, q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective Q)]
    rfl
  have hskder : s.ker ≤ commutator (X ⧸ Q) := by
    rw [hsKer, ← hdermap]
    exact map_mono hderived
  have hperfect : Group.IsPerfect (X ⧸ Q) := by
    constructor
    have hm : (commutator (X ⧸ Q)).map s = ⊤ := by
      rw [map_commutator_eq, s.range_eq_top_of_surjective hs]
      exact Group.IsPerfect.commutator_eq_top
    have he := congrArg (comap s) hm
    rw [comap_map_eq, sup_of_le_left hskder, comap_top] at he
    exact he
  exact ⟨Q, hQnormal, hQp, s, hs, rfl, hscenter, hscard, hperfect⟩

private theorem core_bot {X S : Type*} [Group X] [Finite X] [Group S]
    (s : X →* S) (hs : Function.Surjective s) (hcard : Nat.card s.ker = 3)
    (hS : pCore 2 S = ⊥) : pCore 2 X = ⊥ := by
  have hn : ((pCore 2 X).map s).Normal := Normal.map inferInstance s hs
  have hm : (pCore 2 X).map s ≤ pCore 2 S := le_sSup ⟨hn, pCore_isPGroup.map s⟩
  have hk : pCore 2 X ≤ s.ker := (Subgroup.map_eq_bot_iff _).mp
    (bot_unique (hS ▸ hm))
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) (pCore 2 X) s.ker
    pCore_isPGroup (IsPGroup.of_card (n := 1) (by simpa using hcard))
  exact bot_unique ((le_inf le_rfl hk).trans hd.le_bot)

private theorem residual_equiv {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    [Group.IsPerfect Y] (f : X →* Y) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hY : pCore 2 Y = ⊥) :
    ∃ e : ((solvableResidual X) ⧸ pCore 2 (solvableResidual X)) ≃* Y,
      ∀ x : solvableResidual X,
        e (QuotientGroup.mk' (pCore 2 (solvableResidual X)) x) = f x := by
  let r := f.comp (solvableResidual X).subtype
  have hr : Function.Surjective r := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype, map_solvableResidual_eq f hf,
      solvableResidual_eq_top]
  have hkr : IsPGroup 2 r.ker := by
    rw [← MonoidHom.comap_ker]
    exact hk.comap_of_injective _ (solvableResidual X).subtype_injective
  have he : r.ker = pCore 2 (solvableResidual X) := by
    have he := r.comap_pCore_of_ker_isPGroup hr hkr
    rw [hY, MonoidHom.comap_bot] at he
    exact he
  let e := QuotientGroup.liftEquiv (pCore 2 (solvableResidual X)) hr he.symm
  exact ⟨e, fun _ => rfl⟩

public theorem exists_residual_cover {X H S : Type*} [Group X] [Finite X] [Group H]
    [Group S] [Group.IsPerfect S]
    (f : X →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center X) (hcard : Nat.card f.ker = 3)
    (hderived : f.ker ≤ commutator X)
    (r : H →* S) (hr : Function.Surjective r)
    [IsMulCommutative r.ker] (hR : IsPGroup 2 r.ker)
    (hS : pCore 2 S = ⊥) :
    ∃ t : (solvableResidual X ⧸ pCore 2 (solvableResidual X)) →* S,
      Function.Surjective t ∧
      t.ker ≤ center (solvableResidual X ⧸ pCore 2 (solvableResidual X)) ∧
      Nat.card t.ker = 3 ∧
      ∀ x : solvableResidual X,
        t (QuotientGroup.mk' (pCore 2 (solvableResidual X)) x) = r (f x) := by
  obtain ⟨Q, hQ, hQp, s, hs, hsq, hsc, hsk, hperfect⟩ :=
    splitting f hf hcentral hcard hderived r hr hR
  let := hQ
  let := hperfect
  let q := QuotientGroup.mk' Q
  have hqker : IsPGroup 2 q.ker := by rwa [QuotientGroup.ker_mk']
  obtain ⟨e, he⟩ := residual_equiv q (QuotientGroup.mk'_surjective Q) hqker
    (core_bot s hs hsk hS)
  let t := s.comp e.toMonoidHom
  have htker : t.ker = s.ker.comap e.toMonoidHom := MonoidHom.comap_ker _ _
  refine ⟨t, hs.comp e.surjective, ?_, ?_, ?_⟩
  · intro x hx
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simp only [map_mul]
    exact mem_center_iff.mp (hsc hx) (e y)
  · have hm : t.ker.map e.toMonoidHom = s.ker := by
      rw [htker, map_comap_eq_self_of_surjective e.surjective]
    rw [← hsk, ← hm, card_map_of_injective e.injective]
  · intro x
    change s (e (QuotientGroup.mk' (pCore 2 (solvableResidual X)) x)) = _
    rw [he]
    exact DFunLike.congr_fun hsq x.val

/-- The original cubic kernel lies in the solvable residual itself. -/
public theorem kernel_le_solvableResidual {X H S : Type*} [Group X] [Finite X] [Group H]
    [Group S] [Group.IsPerfect S]
    (f : X →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center X) (hcard : Nat.card f.ker = 3)
    (hderived : f.ker ≤ commutator X)
    (r : H →* S) (hr : Function.Surjective r)
    [IsMulCommutative r.ker] (hR : IsPGroup 2 r.ker) :
    f.ker ≤ solvableResidual X := by
  obtain ⟨Q, hQ, hQp, _, _, _, _, _, hperfect⟩ :=
    splitting f hf hcentral hcard hderived r hr hR
  let := hQ
  let := hperfect
  let q := QuotientGroup.mk' Q
  have hRq : (solvableResidual X).map q = ⊤ := by
    rw [map_solvableResidual_eq q (QuotientGroup.mk'_surjective Q), solvableResidual_eq_top]
  have hjoin : solvableResidual X ⊔ Q = ⊤ := by
    have he := congrArg (comap q) hRq
    rwa [comap_map_eq, QuotientGroup.ker_mk', comap_top] at he
  let w := QuotientGroup.mk' (solvableResidual X)
  have hQw : Q.map w = ⊤ := by
    have he := congrArg (map w) hjoin
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      ← MonoidHom.range_eq_map, w.range_eq_top_of_surjective (QuotientGroup.mk'_surjective _)] at he
  have hw : IsPGroup 2 (X ⧸ solvableResidual X) :=
    (hQw ▸ hQp.map w).of_equiv topEquiv
  have hthree : IsPGroup 3 (f.ker.map w) :=
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hcard)).map w
  have hbot : f.ker.map w = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) (f.ker.map w) (f.ker.map w)
      (hw.to_subgroup _) hthree
    simpa only [inf_idem] using hd.eq_bot
  have hk := (Subgroup.map_eq_bot_iff _).mp hbot
  rwa [QuotientGroup.ker_mk'] at hk

end CubicCentralRestriction
