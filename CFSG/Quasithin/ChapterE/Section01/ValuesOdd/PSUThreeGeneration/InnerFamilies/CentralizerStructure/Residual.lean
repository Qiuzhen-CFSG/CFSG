module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerActors
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.SolvableResidual.Transport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.Projective

/-!
# Residuals of the full inner-involution centralizer and its Sylow supplement

If G = LT with L normal, the full centralizer has two-group quotient by
its intersection with L. Its solvable residual is therefore exactly the
embedded residual of the intrinsic L-centralizer. The checked projective
calculation identifies this with SL₂(p) for p > 3.

The subgroup C_G(z)^∞T has the same solvable residual, and its two-residual
equals that residual. This equality is not asserted for the full centralizer.
Source: Aschbacher--Smith A.3.21(a), p.55, and E.1.2(E2), p.210.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The local supplement lies in the full centralizer. -/
theorem centralizerResidualOvergroup_le {T : Sylow 2 G} {z : G}
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    centralizerResidualOvergroup T z ≤ centralizer ({z} : Set G) :=
  sup_le (map_subtype_le _) hTz

/-- The equality O²(K) = K^∞ for the literal residual supplement K. -/
theorem centralizerResidualOvergroup_pResidual_eq {T : Sylow 2 G} {z : G}
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    pResidual 2 (centralizerResidualOvergroup T z) =
      solvableResidual (centralizerResidualOvergroup T z) := by
  let C := centralizer ({z} : Set G)
  let D := (solvableResidual C).map C.subtype
  let : Group.IsPerfect D := Group.IsPerfect.map C.subtype
  have hn : C ≤ normalizer (D : Set G) := by
    have h := (solvableResidual C).le_normalizer_map C.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
  exact pResidual_eq_solvableResidual_of_perfect_sup_twoGroup D T T.isPGroup' (hTz.trans hn)

/-- The full centralizer and its residual supplement have the same embedded residual. -/
theorem centralizerResidualOvergroup_residual_map {T : Sylow 2 G} {z : G}
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    (solvableResidual (centralizerResidualOvergroup T z)).map
        (centralizerResidualOvergroup T z).subtype =
      (solvableResidual (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype := by
  let C := centralizer ({z} : Set G)
  let D := (solvableResidual C).map C.subtype
  let : Group.IsPerfect D := Group.IsPerfect.map C.subtype
  exact le_antisymm (map_solvableResidual_mono (centralizerResidualOvergroup_le hTz))
    (le_map_solvableResidual_of_isPerfect D _ le_sup_left)

/-- The inclusion of the residual supplement identifies its residual with that of C. -/
noncomputable def centralizerResidualOvergroup_residualEquiv {T : Sylow 2 G} {z : G}
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    solvableResidual (centralizerResidualOvergroup T z) ≃*
      solvableResidual (centralizer ({z} : Set G)) :=
  ((solvableResidual _).equivMapOfInjective
    (centralizerResidualOvergroup T z).subtype (centralizerResidualOvergroup T z).subtype_injective).trans
    ((MulEquiv.subgroupCongr (centralizerResidualOvergroup_residual_map hTz)).trans
      ((solvableResidual _).equivMapOfInjective
        (centralizer ({z} : Set G)).subtype (centralizer ({z} : Set G)).subtype_injective).symm)

/-- The residual of the full ambient centralizer is SL₂(p), for every two-extension. -/
theorem inner_centralizer_residual_equiv (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hlarge : 3 < p)
    (hmodel : ClassicalGroup.IsPSU L 3 p) (z : G) (hzL : z ∈ L) (hz : orderOf z = 2) :
    Nonempty (solvableResidual (centralizer ({z} : Set G)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  let : Fact p.Prime := ⟨hp⟩
  let C := centralizer ({z} : Set G)
  let f := (QuotientGroup.mk' L).comp C.subtype
  let N := f.ker
  have hq := isPGroup_quotient_of_sup_eq_top L T T.isPGroup' hLT
  have hN : IsPGroup 2 (C ⧸ N) :=
    (hq.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  let : Group.IsNilpotent (C ⧸ N) := hN.isNilpotent
  let w : L := ⟨z, hzL⟩
  let e : N ≃* centralizer ({w} : Set L) :=
    { toFun := fun x => ⟨⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩,
        mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
      invFun := fun x => ⟨⟨x.val.val, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,
        (QuotientGroup.eq_one_iff _).mpr x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  obtain ⟨es⟩ := Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition.isPSU_involution_solvableResidual
    p hodd hlarge hmodel w ((orderOf_submonoid w).symm.trans hz)
  exact ⟨(solvableResidualEquivOfSolvableQuotient N).symm.trans
    (e.solvableResidualEquiv.trans es)⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
