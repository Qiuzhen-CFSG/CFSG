module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.PrimeByTwo
public import CFSG.Quasithin.Chapter3.Section01.Source318Guarded
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.StarNormalizer

/-!
# The guarded ratio contradiction for the original enlarged odd radical

Let X be the original starred canonical radical and X≤I≤N_G(X), with
I normal in N_G(X) and two-perfect. Uniqueness over XT gives uniqueness
over IT. The genuine standing guard therefore lets 3.1.8 bound the
literal conjugation action on an original reduced subgroup of IT.
When I/O₂(I) is a p-group, D.2.13 forces p=3 or p=5. The proof does not
replace I with X or assume the enlarged radical is itself a Xi member.

Source: Aschbacher--Smith 3.2.14, final paragraph, p.585.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.RadicalCentralization
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source enlarged radical, with its literal reduced module and
Sylow centralizer, satisfies the original D.2.13 prime bound. -/
theorem prime_restriction_of_guarded_star
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (h318 : GuardedSourceTheorem318One G)
    {X I : Subgroup G} (hX : X ∈ Chapter1.XiStar G (T : Subgroup G))
    (hXI : X ≤ I) (hIM : I ≤ normalizer (X : Set G))
    (hn : normalizer (X : Set G) ≤ normalizer (I : Set G)) (hIp : IsPPerfect 2 I)
    (hout : HasMaximalOutside T (normalizer (X : Set G)))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hI : IsPGroup p (I ⧸ pCore 2 I))
    (W : Subgroup (I ⊔ (T : Subgroup G) : Subgroup G)) (hW : IsPReduced 2 W)
    (hc : (T : Subgroup G).subgroupOf (I ⊔ (T : Subgroup G)) ⊓
      centralizer (W : Set (I ⊔ (T : Subgroup G) : Subgroup G)) =
        pCore 2 (I ⊔ (T : Subgroup G) : Subgroup G)) : p = 3 ∨ p = 5 := by
  obtain ⟨hmax,hu⟩ := Chapter1.XiEmbedding.normalizer_unique_of_XiStar_knownSimple hG T hX
  have hTM : (T : Subgroup G) ≤ normalizer (X : Set G) := hX.1.invariant
  have hJM : I ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) := sup_le hIM hTM
  have huniq (N : Subgroup G) (hN : IsMaximalTwoLocal N)
      (hIN : I ⊔ (T : Subgroup G) ≤ N) : N = normalizer (X : Set G) := by
    have hh : N ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ X ⊔ (T : Subgroup G) ≤ M} :=
      ⟨hN,(sup_le_sup_right hXI _).trans hIN⟩
    rw [hu] at hh
    exact Set.mem_singleton_iff.mp hh
  have hAt := sourceTheorem318OneAt_of_guarded h318 hmax hTM hout
  have hr := hAt.cubicRatio_le I hIp hIM (normal_subgroupOf_of_le_normalizer hn)
    hmax hJM huniq W hW hc
  let J := I ⊔ (T : Subgroup G)
  let I₀ := I.subgroupOf J
  let T₀ := (T : Subgroup G).subgroupOf J
  let : I₀.Normal := normal_subgroupOf_of_le_normalizer (hJM.trans hn)
  have hgen : I₀ ⊔ T₀ = ⊤ := by
    rw [← subgroupOf_sup (show I ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self _
  let e : I₀ ≃* I := subgroupOfEquivOfLe (show I ≤ J from le_sup_left)
  let eq : (I₀ ⧸ pCore 2 I₀) ≃* (I ⧸ pCore 2 I) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  exact ChapterD.prime_restriction_of_reduced_extension I₀ T₀ hgen ho
    (hI.of_equiv eq.symm) T.isPGroup'.comap_subtype W hW hr

end CFSG.Quasithin.Chapter3.RadicalCentralization
