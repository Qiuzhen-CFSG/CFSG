module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.NaturalSetup
/-!
# Constructing the reduced natural-block setup

The original block model supplies the field and central-cover projection.
Its actual normalizer image, the reduced semilinear Baumann theorem, and the
marked Sylow quotient construct every field of Setup(T,K,F), including the
internal action of S∩K. The field is extracted from the original block type.

Source: Aschbacher–Smith C.5.4 and C.5.9, printed pp.155 and161.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

theorem exists_linear_reduced_setup (K T : Subgroup G) {n : ℕ} (hK : IsL2EvenBlock K n)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (hno : ∀ N : Subgroup G, N ≤ T → normalizer (T : Set G) ≤ normalizer (N : Set G) →
      K ⊔ T ≤ normalizer (N : Set G) → N = ⊥) :
    ∃ (F : Type) (_ : Field F), Nonempty (Setup T K F) := by
  have hKn := hK
  obtain ⟨hnlarge,hshort,F,_,_,hF,_,τ,⟨m⟩,hτ⟩ := hK
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hlarge : 2 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    rw [hF]
    norm_num at hh ⊢
    omega
  obtain ⟨β,hβ,hβker,hβK,hβS,hsyl⟩ :=
    natural_reduced_action_and_sylow K T hshort hT hn P hP hmin hno τ m hτ hlarge
  obtain ⟨q,π,hq,hπ,hker,hπker,himage,hKimage,he⟩ :=
    natural_marked_quotient K T (inf_le_left.trans hn) τ m hτ β hβ hβker hβK hβS hsyl
  exact ⟨F,inferInstance,setup_of_natural_quotient K T (Or.inl ⟨n,hKn⟩)
    (inf_le_left.trans hn) hsyl τ hτ q π hq hπ hker hπker himage (Or.inl hKimage) he⟩
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
