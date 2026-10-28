module
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.SylowKernelCore
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# A cubic fixed subgroup in an intersecting two-kernel

Let a finite group map onto a group in which the cubic fixes at most two
points of the two-core. Suppose the elementary kernel has order 64 and
its cubic fixed subgroup has order at most four. Then the cubic fixes at
most eight points of the original two-core. If a second normal two-subgroup
contains all two-core commutators but not the whole elementary kernel,
coprime decomposition supplies a fixed kernel element outside it. Its
fixed subgroup is therefore proper in the group of order at most eight,
and has order at most four.

Only relative normality inside the original finite group is used. The two
kernels are kept distinct. The original Rudvalis point-stabilizer application
is in Chapter13's OriginalOddNormalizer.RudvalisCubicIntersection.
Source: Aschbacher--Smith 4.2.13, printed p.612.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- The literal second kernel has cubic fixed subgroup of order at most four. -/
theorem cubic_kernel_intersection_fixed_card_le_four
    (b : G →* H) (hb : Function.Surjective b) [IsElementaryAbelian 2 b.ker]
    (hbk : Nat.card b.ker = 64)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
    (hnot : ¬ b.ker ≤ R) (hcomm : ⁅pCore 2 G,⊤⁆ ≤ R)
    (x : G) (hx : orderOf x = 3)
    (hfixed : Nat.card (b.ker ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 4)
    (hmodel : Nat.card (pCore 2 H ⊓ centralizer ({b x} : Set H) : Subgroup H) ≤ 2) :
    Nat.card (R ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 4 := by
  let C := pCore 2 G ⊓ centralizer ({x} : Set G)
  let D := R ⊓ centralizer ({x} : Set G)
  have hE : b.ker ≤ pCore 2 G :=
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 b.ker⟩
  have hRcore : R ≤ pCore 2 G := le_sSup ⟨inferInstance,hR⟩
  have hmapCore : (pCore 2 G).map b ≤ pCore 2 H := by
    let : ((pCore 2 G).map b).Normal := Subgroup.Normal.map inferInstance b hb
    exact le_sSup ⟨inferInstance,pCore_isPGroup.map b⟩
  have hmap : C.map b ≤ pCore 2 H ⊓ centralizer ({b x} : Set H) := by
    rintro y ⟨u,hu,rfl⟩
    exact ⟨hmapCore (mem_map_of_mem b hu.1),mem_centralizer_singleton_iff.mpr
      (by simpa only [map_mul] using congrArg b (mem_centralizer_singleton_iff.mp hu.2))⟩
  have hker : C ⊓ b.ker ≤ b.ker ⊓ centralizer ({x} : Set G) := by
    rintro y ⟨hy,he⟩
    exact ⟨he,hy.2⟩
  have hC : Nat.card C ≤ 8 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map C b
    have h1 := (card_le_of_le hker).trans hfixed
    have h2 := (card_le_of_le hmap).trans hmodel
    nlinarith
  have hnorm : zpowers x ≤ normalizer (b.ker : Set G) := le_normalizer_of_normal
  have hcop : Nat.Coprime (Nat.card (zpowers x)) (Nat.card b.ker) := by
    rw [Nat.card_zpowers,hx,hbk]
    decide
  have hsolv : Group.IsSolvable b.ker := by
    let := (IsElementaryAbelian.isPGroup 2 b.ker).isNilpotent
    infer_instance
  have hdecomp := eq_commutator_sup_centralizer_of_solvable_coprime
    b.ker (zpowers x) hnorm hsolv hcop
  rw [zpowers_eq_closure,centralizer_closure] at hdecomp
  have hescape : ¬ C ≤ R := by
    intro hc
    apply hnot
    rw [hdecomp]
    exact sup_le ((commutator_mono hE le_top).trans hcomm)
      ((inf_le_inf_right _ hE).trans hc)
  have hDC : D ≤ C := inf_le_inf_right _ hRcore
  by_contra! hlarge
  change 4 < Nat.card D at hlarge
  have he : Nat.card C = Nat.card D :=
    Nat.eq_of_dvd_of_lt_two_mul Nat.card_pos.ne' (card_dvd_of_le hDC) (by omega)
  have hsame : D = C := eq_of_le_of_card_ge hDC he.le
  exact hescape (hsame ▸ (show D ≤ R from inf_le_left))
end Theory.GroupTheory
