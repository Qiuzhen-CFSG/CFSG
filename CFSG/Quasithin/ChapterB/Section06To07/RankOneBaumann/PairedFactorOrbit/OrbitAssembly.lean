module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.FirstAxisSpan
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.AlphaBound
public import Theory.Representation.BinaryOffender.PPerfectFixedLift
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.GroupTheory.ConjugateSpanOrder
/-!
# The exact first-factor orbit identity

The two natural fixed lines give the lower inclusion and the derived
alpha decomposition gives the upper inclusion, with normalization of
the original commutator subgroup. All factors and maps remain literal.
Source: Aschbacher–Smith B.6.10/E.2.3, pp.117 and216–217.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
open QuasisimpleSource
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
variable (F : BinaryField)
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F.Carrier
local notation "V" => Fin 2 → F.Carrier
local notation "N" => linearNatural F 2

omit [Finite G] [Finite H] in
theorem first_factor_orbit_of_coordinates
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (J E R K : Subgroup G) (hKR : K ≤ R) (hK : IsPPerfect 2 K)
    (hE : E = (E ⊓ centralizer (R : Set G)) ⊔ (U ⊓ centralizer (J : Set G)))
    (f : Additive U →ₗ[ZMod 2] (V × V)) (hf : Function.Surjective f)
    (j : D →* H)
    (himage : K.map q = (pResidual 2 D).map j)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker (j g) v) =
      (N g (f v).1,(f v).2))
    (hk : f.ker ≤ fixedSpace (NormalElementaryQuotient.representation U q hq hker) (K.map q))
    (P Q : Sylow 2 D)
    (hfix : fixedSpace (NormalElementaryQuotient.representation U q hq hker) (J.map q) =
      ((fixedSpace N (P : Subgroup D)).prod (fixedSpace N (Q : Subgroup D))).comap f) :
    conjugateSpanBy E K = (⁅U,K⁆ : Subgroup G) ⊔ (E ⊓ centralizer (K : Set G)) := by
  have hMO := first_axis_moved_le_orbit F U q hq hker J E K
    (le_sup_right.trans hE.ge) f hf j himage he P Q hfix
  have hEle := first_factor_alpha_le_commutator_fixed F U q hq hker J E R K hKR hK
    hE f hf j himage he hk P Q hfix
  apply le_antisymm
  · apply conjugateSpanBy_le hEle
    have hKC : K ≤ normalizer (E ⊓ centralizer (K : Set G) : Set G) :=
      (le_centralizer_iff.mp inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
    have hKM : K ≤ normalizer (⁅U,K⁆ : Subgroup G) := by
      intro k hk'
      rw [mem_normalizer_iff_map_conj_eq,map_commutator,
        Normal.map_conj_eq U k,mem_normalizer_iff_map_conj_eq.mp (K.le_normalizer hk')]
    exact (le_inf hKM hKC).trans (normalizer_inf_normalizer_le_normalizer_sup (⁅U,K⁆ : Subgroup G) (E ⊓ centralizer (K : Set G)))
  · exact sup_le hMO (inf_le_left.trans (le_conjugateSpanBy E K))
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
