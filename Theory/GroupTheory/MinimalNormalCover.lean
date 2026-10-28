module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Coverage of a self-centralizing minimal normal subgroup

Every nontrivial normal subgroup contains a self-centralizing minimal normal
subgroup: otherwise their commutator lies in their trivial intersection.
If the minimal normal subgroup is an odd prime group, the two-core is trivial.
For a normal envelope V containing E, failure of N(E) to cover this minimal
normal section therefore puts C(V) in the kernel of the original quotient map.

Source: GLS, *The Classification of the Finite Simple Groups*, Number 2,
G.26.18(a), proof, printed pp.152–153. These are the normal-section deductions
used for the constructed elementary module.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A self-centralizing minimal normal subgroup is contained in every
nontrivial normal subgroup. -/
theorem normal_eq_bot_of_not_covering_minimal
    (Y U : Subgroup G) [Y.Normal] [U.Normal]
    (hmin : ∀ D : Subgroup G, D.Normal → D ≤ Y → D = ⊥ ∨ D = Y)
    (hself : centralizer (Y : Set G) ≤ Y) (hn : ¬ Y ≤ U) : U = ⊥ := by
  have hi : U ⊓ Y = ⊥ := (hmin _ inferInstance inf_le_right).resolve_right
    (fun he => hn (he ▸ (show U ⊓ Y ≤ U from inf_le_left)))
  have hc : U ≤ centralizer (Y : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (bot_unique ((commutator_le_inf U Y).trans hi.le))
  exact bot_unique ((le_inf le_rfl (hc.trans hself)).trans hi.le)

theorem twoCore_eq_bot_of_odd_minimal_selfCentralizing
    (Y : Subgroup G) [Y.Normal] {r : ℕ} [Fact r.Prime]
    (hY : IsPGroup r Y) (hr : Odd r) (hne : Y ≠ ⊥)
    (hmin : ∀ D : Subgroup G, D.Normal → D ≤ Y → D = ⊥ ∨ D = Y)
    (hself : centralizer (Y : Set G) ≤ Y) : pCore 2 G = ⊥ := by
  apply normal_eq_bot_of_not_covering_minimal Y _ hmin hself
  intro hle
  have hd := (pCore_isPGroup (p := 2) (G := G)).disjoint_of_coprime hY
    (Nat.coprime_two_left.mpr hr)
  exact hne (bot_unique ((le_inf hle le_rfl).trans hd.eq_bot.le))

/-- A normal elementary envelope containing E has kernel contained in I
when N(E) does not cover the self-centralizing minimal normal section. -/
theorem centralizer_le_kernel_of_normalizer_not_covering
    {H : Type*} [Group H] (q : G →* H) (hq : Function.Surjective q)
    (Y : Subgroup H) [Y.Normal]
    (hmin : ∀ D : Subgroup H, D.Normal → D ≤ Y → D = ⊥ ∨ D = Y)
    (hself : centralizer (Y : Set H) ≤ Y)
    (E V : Subgroup G) [V.Normal] (hEV : E ≤ V)
    (hn : ¬ Y ≤ (normalizer (E : Set G)).map q) :
    centralizer (V : Set G) ≤ q.ker := by
  have hc : centralizer (V : Set G) ≤ normalizer (E : Set G) :=
    (centralizer_le hEV).trans (Subgroup.centralizer_le_normalizer _)
  let : ((centralizer (V : Set G)).map q).Normal := Normal.map inferInstance q hq
  exact (map_eq_bot_iff (centralizer (V : Set G))).mp
    (normal_eq_bot_of_not_covering_minimal Y ((centralizer (V : Set G)).map q) hmin hself
      (fun hh => hn (hh.trans (map_mono hc))))
end Theory.GroupTheory
