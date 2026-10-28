module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.Commutator.SubnormalAbsorption
public import Mathlib.Algebra.Group.Pi.Lemmas

open Subgroup CFSG.Quasithin.ChapterC
open scoped commutatorElement
/-!
# Irreducible short subgroups in powers of a Borel seed

A two-perfect seed with simple quotient by a normal two-subgroup has no
proper nontrivial subnormal two-perfect subgroup. Consequently every
coordinate image of a short subgroup is trivial or the full seed.

When the seed is centerless and its nontrivial normal two-subgroup P
satisfies [P,K] = P, subnormal commutator absorption places each active
coordinate copy of P inside U(D). The center of D is trivial. Irreducibility
of U(D)/C_U(D) then excludes two active coordinates, giving a whole factor.
This is the short-block argument for the A₄ Borel; perfectness of the seed
is not assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7 and
C.1.12, printed pp.123–124; the orbit application is E.6.7–8, pp.246–248.
-/

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.OrbitFactors

private theorem image_top {K : Type*} [Group K] {p : ℕ}
    (hK : IsPPerfect p K) (P : Subgroup K) [P.Normal]
    [IsSimpleGroup (K ⧸ P)] (hP : IsPGroup p P)
    (D : Subgroup K) (hs : D.IsSubnormal) (hp : IsPPerfect p D) (hne : D ≠ ⊥) :
    D = ⊤ := by
  let q := QuotientGroup.mk' P
  rcases (hs.map (QuotientGroup.mk'_surjective P)).eq_bot_or_top_of_isSimpleGroup
      inferInstance with hz | ht
  · have hDP : D ≤ P := by
      simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff D).mp hz
    have hquot : IsPGroup p (D ⧸ (⊥ : Subgroup D)) :=
      (hP.to_le hDP).of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective _)
    have hbot : (⊥ : Subgroup D) = ⊤ := hp _ inferInstance hquot
    apply (hne _).elim
    apply le_bot_iff.mp
    intro x hx
    have hh : (⟨x, hx⟩ : D) ∈ (⊥ : Subgroup D) := hbot.symm ▸ mem_top _
    exact congrArg Subtype.val (mem_bot.mp hh)
  · have hprod : ∀ g : K, ∃ d ∈ D, ∃ r ∈ P, d * r = g := by
      intro g
      obtain ⟨d, hd, he⟩ := mem_map.mp (show q g ∈ D.map q by rw [ht]; trivial)
      exact ⟨d, hd, d⁻¹ * g, QuotientGroup.eq.mp he, mul_inv_cancel_left d g⟩
    have he := pResidual_eq_of_subnormal_product D P hs hp hP hprod
    rw [(pResidual_eq_top_iff p K).mpr hK] at he
    exact he.symm

private theorem coordinate_commutator {K I : Type*} [Group K] [DecidableEq I]
    (P : Subgroup K) (D : Subgroup (I → K)) (i : I)
    (hi : D.map (Pi.evalMonoidHom (fun _ : I => K) i) = ⊤) :
    (⁅P, (⊤ : Subgroup K)⁆).map (MonoidHom.mulSingle (fun _ : I => K) i) ≤
      ⁅P.map (MonoidHom.mulSingle (fun _ : I => K) i), D⁆ := by
  let ev := Pi.evalMonoidHom (fun _ : I => K) i
  let s := MonoidHom.mulSingle (fun _ : I => K) i
  rw [map_le_iff_le_comap, commutator_le]
  intro x hx y _
  obtain ⟨d, hd, hdi⟩ := mem_map.mp (show y ∈ D.map ev by rw [hi]; trivial)
  change s ⁅x, y⁆ ∈ ⁅P.map s, D⁆
  have he : s ⁅x, y⁆ = ⁅s x, d⁆ := by
    ext j
    by_cases hij : i = j
    · subst j
      simpa [s, ev, commutatorElement_def] using
        congrArg (fun z => x * z * x⁻¹ * z⁻¹) hdi.symm
    · simp [s, commutatorElement_def, Pi.mulSingle_eq_of_ne (Ne.symm hij)]
  rw [he]
  exact commutator_mem_commutator (mem_map_of_mem _ hx) hd

private theorem coordinate_normal {K I : Type*} [Group K] [DecidableEq I]
    (P : Subgroup K) [P.Normal] (i : I) :
    (P.map (MonoidHom.mulSingle (fun _ : I => K) i)).Normal := by
  constructor
  rintro x ⟨y, hy, rfl⟩ g
  refine mem_map.mpr ⟨g i * y * (g i)⁻¹, (inferInstance : P.Normal).conj_mem y hy (g i), ?_⟩
  ext j
  by_cases hij : i = j
  · subst j
    simp
  · simp [Pi.mulSingle_eq_of_ne (Ne.symm hij)]

private theorem core_coordinate_le_U {K I D : Type*} [Group K] [Group D]
    [DecidableEq I] (P : Subgroup K) [P.Normal] (hp : IsPGroup 2 P)
    (hcomm : ⁅P, ⊤⁆ = P) (f : D →* (I → K)) (hf : Function.Injective f)
    (hs : f.range.IsSubnormal) (i : I)
    (hi : f.range.map (Pi.evalMonoidHom (fun _ : I => K) i) = ⊤) :
    P.map (MonoidHom.mulSingle (fun _ : I => K) i) ≤ (blockU D).map f := by
  let R := P.map (MonoidHom.mulSingle (fun _ : I => K) i)
  have hc : R ≤ ⁅R, f.range⁆ := by
    simpa only [hcomm] using coordinate_commutator P f.range i hi
  have hR : R ≤ f.range := le_of_isSubnormal_of_le_commutator R f.range hs hc
  let : R.Normal := coordinate_normal P i
  have hcore : R.comap f ≤ pCore 2 D :=
    le_sSup ⟨inferInstance, (hp.map _).comap_of_injective f hf⟩
  have hmap : R ≤ (pCore 2 D).map f := by
    rw [← map_comap_eq_self hR]
    exact map_mono hcore
  apply hc.trans
  change ⁅R, f.range⁆ ≤ (⁅pCore 2 D, (⊤ : Subgroup D)⁆).map f
  rw [map_commutator, ← MonoidHom.range_eq_map]
  exact commutator_mono hmap le_rfl


/-- A short subgroup embedded subnormally in a direct power contains an actual
coordinate factor under the stated intrinsic seed conditions. -/
public theorem short_factor {K I D : Type*} [Group K] [Group D] [DecidableEq I]
    (hK : IsPPerfect 2 K) (hZ : center K = ⊥)
    (P : Subgroup K) [P.Normal] [IsSimpleGroup (K ⧸ P)]
    (hP : IsPGroup 2 P) (hne : P ≠ ⊥) (hcomm : ⁅P, ⊤⁆ = P)
    (hD : IsShort D) (f : D →* (I → K)) (hf : Function.Injective f)
    (hs : f.range.IsSubnormal) :
    ∃ i : I, ∀ k : K, Pi.mulSingle i k ∈ f.range := by
  let c : I → D →* K := fun i => (Pi.evalMonoidHom (fun _ : I => K) i).comp f
  have hc (i : I) : c i = 1 ∨ Function.Surjective (c i) := by
    have heval : Function.Surjective (Pi.evalMonoidHom (fun _ : I => K) i) :=
      fun k => ⟨fun _ => k, rfl⟩
    have hsi : (c i).range.IsSubnormal := by
      rw [MonoidHom.range_comp]
      exact hs.map heval
    by_cases hz : (c i).range = ⊥
    · exact Or.inl (MonoidHom.range_eq_bot_iff.mp hz)
    · exact Or.inr (MonoidHom.range_eq_top.mp
        (image_top hK P hP _ hsi
          (hD.twoPerfect.of_surjective (c i).rangeRestrict (c i).rangeRestrict_surjective) hz))
  have hcenter : center D = ⊥ := by
    apply eq_bot_iff.mpr
    intro d hd
    apply mem_bot.mpr
    apply hf
    rw [map_one]
    funext i
    rcases hc i with hi | hi
    · exact DFunLike.congr_fun hi d
    · have hz : c i d ∈ center K := by
        apply mem_center_iff.mpr
        intro k
        obtain ⟨a, rfl⟩ := hi k
        simpa only [map_mul] using congrArg (c i) (mem_center_iff.mp hd a)
      exact mem_bot.mp (hZ ▸ hz)
  have hbase : blockU D ⊓ center D = ⊥ := by rw [hcenter, inf_bot_eq]
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha1 : a ≠ 1 := fun hh => ha1 (Subtype.ext hh)
  have hcore (i : I) (hi : Function.Surjective (c i)) :
      P.map (MonoidHom.mulSingle (fun _ : I => K) i) ≤ (blockU D).map f := by
    apply core_coordinate_le_U P hP hcomm f hf hs i
    change f.range.map (Pi.evalMonoidHom (fun _ : I => K) i) = ⊤
    rw [← MonoidHom.range_comp]
    exact MonoidHom.range_eq_top.mpr hi
  obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD.blockU_ne_bot
  have hfd : f d ≠ 1 := fun hh => hd1 (Subtype.ext (hf (hh.trans (map_one f).symm)))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hfd
  have his : Function.Surjective (c i) := (hc i).resolve_left
    (fun hh => hi (DFunLike.congr_fun hh d))
  let N := blockU D ⊓ (c i).ker
  have hn : N = ⊥ := by
    rcases hD.irreducible.2 N inferInstance (hbase ▸ bot_le) inf_le_left with hn | hn
    · exact hn.trans hbase
    · obtain ⟨x, hx, hfx⟩ := mem_map.mp (hcore i his (mem_map_of_mem _ ha))
      have hxi : c i x = 1 := (show x ∈ (c i).ker from (hn ▸ hx : x ∈ N).2)
      have hai : a = 1 := by
        have hh := congrFun hfx i
        simpa only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same] using hh.symm.trans hxi
      exact (ha1 hai).elim
  have hother (j : I) (hji : j ≠ i) : c j = 1 := by
    rcases hc j with hj | hj
    · exact hj
    · obtain ⟨x, hx, hfx⟩ := mem_map.mp (hcore j hj (mem_map_of_mem _ ha))
      have hxi : c i x = 1 := by
        have hh := congrFun hfx i
        simpa [c, Pi.mulSingle_eq_of_ne (Ne.symm hji)] using hh
      have hx1 : x = 1 := mem_bot.mp (hn ▸ (show x ∈ N from ⟨hx, hxi⟩))
      have hai : a = 1 := by
        have hh := congrFun hfx j
        simpa only [hx1, map_one, Pi.one_apply, MonoidHom.mulSingle_apply,
          Pi.mulSingle_eq_same] using hh.symm
      exact (ha1 hai).elim
  refine ⟨i, fun k => ?_⟩
  obtain ⟨x, hx⟩ := his k
  refine ⟨x, funext fun j => ?_⟩
  by_cases hji : j = i
  · subst j
    simpa [c] using hx
  · have hh := DFunLike.congr_fun (hother j hji) x
    simpa [c, Pi.mulSingle_eq_of_ne hji] using hh

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.OrbitFactors
