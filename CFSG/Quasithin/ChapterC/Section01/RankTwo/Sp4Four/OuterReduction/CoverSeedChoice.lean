module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.SmallSeedChoice
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowSeedCard

/-!
# The source endpoint does not normalize the literal fixed cover seed

The full source Sylow image fixes at most q squared vectors on the original
central cover. At q=4 the actual U_delta intersect C(S*) seed therefore has
order at most16. Its common edge normalizes it. The component small-section
argument forces the chosen endpoint to fail to normalize its join with
Z_alpha whenever the residual displacement is bad.

Source: MS93 (2.1)(vii),(3.4), p.868. This discharges the seed-order premise
and uses only the component's simple quotient, before outer removal. The
chosen critical generating pair remains the earlier graph input.
-/

public section

open Subgroup Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M F : Type*} [Group M] [Finite M] {R : Subgroup M}
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

theorem endpoint_not_normalizes_cover_seed (geometry : Geometry R)
    (hb : 0 < geometry.b R) {a d t e : Vertex R}
    (ha : color R a = false) (hd : color R d = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hp : IsPGroup 2 (Q R t))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : Ltilde R a →* S) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S)
    (T : Subgroup (FreeAmalgam R)) [Finite (U R d)] [IsElementaryAbelian 2 (U R d)]
    (π : T →* L (K := F)) (P : Sylow 2 (L (K := F)))
    (himage : π.range = (P : Subgroup (L (K := F))))
    (σ : Representation (ZMod 2) (L (K := F)) (Additive (U R d)))
    (hact : ∀ s : T, ∀ u : U R d,
      ((σ (π s) (Additive.ofMul u)).toMul : FreeAmalgam R) =
        (s:FreeAmalgam R)*u*(s:FreeAmalgam R)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hpcover : IsCover p)
    (hF : Nat.card F = 4)
    (hbad : ¬ ⁅U R d ⊓ centralizer (T : Set (FreeAmalgam R)),Ltilde R a⁆ ≤ Z R a)
    (hT : Q R t ≤ normalizer (T : Set (FreeAmalgam R)))
    (hgen : stabilizer R a ≤ Q R t ⊔ Z R e) :
    ¬ Z R e ≤ normalizer
      (((U R d ⊓ centralizer (T : Set (FreeAmalgam R))) ⊔ Z R a :
        Subgroup (FreeAmalgam R)) : Set _) := by
  have hcard := centralizer_cover_sylow_card_le (U R d) T π P himage σ hact p hpcover
  rw [hF] at hcard
  have hnU : Q R t ≤ normalizer (U R d : Set (FreeAmalgam R)) :=
    (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt)).trans
      (U_normalized d)
  have hnC : normalizer (T : Set (FreeAmalgam R)) ≤
      normalizer (centralizer (T : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance
  exact endpoint_not_normalizes_bad_seed_of_card geometry hb ha hd hat hdt hp q hq hker hS
    (U R d ⊓ centralizer (T : Set (FreeAmalgam R))) inf_le_left
    (hcard.trans (by norm_num)) hbad
    ((le_inf hnU (hT.trans hnC)).trans inf_normalizer_le_normalizer_inf) hgen

theorem endpoint_not_normalizes_embedded_cover_seed (geometry : Geometry R)
    (hb : 0 < geometry.b R) {a d t e : Vertex R}
    (ha : color R a = false) (hd : color R d = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hp : IsPGroup 2 (Q R t))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : Ltilde R a →* S) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S)
    (T : Subgroup (FreeAmalgam R))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (j : Multiplicative W →* FreeAmalgam R) (hj : Function.Injective j) (hjU : j.range = U R d)
    (π : T →* L (K := F)) (P : Sylow 2 (L (K := F)))
    (himage : π.range = (P : Subgroup (L (K := F))))
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (hact : ∀ s : T, ∀ w : W,
      j (Multiplicative.ofAdd (σ (π s) w)) =
        (s:FreeAmalgam R)*j (Multiplicative.ofAdd w)*(s:FreeAmalgam R)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hpcover : IsCover p)
    (hF : Nat.card F = 4)
    (hbad : ¬ ⁅U R d ⊓ centralizer (T : Set (FreeAmalgam R)),Ltilde R a⁆ ≤ Z R a)
    (hT : Q R t ≤ normalizer (T : Set (FreeAmalgam R)))
    (hgen : stabilizer R a ≤ Q R t ⊔ Z R e) :
    ¬ Z R e ≤ normalizer
      (((U R d ⊓ centralizer (T : Set (FreeAmalgam R))) ⊔ Z R a :
        Subgroup (FreeAmalgam R)) : Set _) := by
  have hcard := centralizer_embedded_cover_sylow_card_le (U R d) T j hj hjU π P himage σ hact p hpcover
  rw [hF] at hcard
  have hnU : Q R t ≤ normalizer (U R d : Set (FreeAmalgam R)) :=
    (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt)).trans
      (U_normalized d)
  have hnC : normalizer (T : Set (FreeAmalgam R)) ≤
      normalizer (centralizer (T : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance
  exact endpoint_not_normalizes_bad_seed_of_card geometry hb ha hd hat hdt hp q hq hker hS
    (U R d ⊓ centralizer (T : Set (FreeAmalgam R))) inf_le_left
    (hcard.trans (by norm_num)) hbad
    ((le_inf hnU (hT.trans hnC)).trans inf_normalizer_le_normalizer_inf) hgen

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
