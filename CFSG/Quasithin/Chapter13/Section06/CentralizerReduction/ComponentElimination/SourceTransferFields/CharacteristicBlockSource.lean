module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.MinimalParabolicSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry
/-!
# The characteristic-normalizer source for local block consumers

The strict normalizer obstruction of 13.6.16(2) excludes every nontrivial
characteristic Sylow subgroup from being normal in the actual local join.
The Chapter C orbit theorem therefore supplies its full residual block
product. Local C-component rigidity identifies the selected component as
a factor, and perfectness removes the alternating-three case.

These are literal consumers on K ∨ S, using the actual Sylow embedding.
They discharge the C.1.26 input needed in 13.6.18–19 without changing the
existing distinguished-pair API.
Source: Aschbacher–Smith C.1.26, printed p.132; 13.6.16–19, pp.930–931.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
open ComponentSelection HigherFieldParabolics
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
universe u
variable {G : Type u} [Group G] [Finite G]

theorem residual_product_of_characteristic_obstruction
    (S K : Subgroup G)
    (hpush : CharacteristicNormalizerObstruction S K)
    (hsqtk : IsSQTK KnownSimple.IsKnownSimple (K ⊔ S : Subgroup G))
    (hf : generalizedFitting (K ⊔ S : Subgroup G) = pCore 2 (K ⊔ S : Subgroup G))
    (P : Sylow 2 (K ⊔ S : Subgroup G))
    (hP : (P : Subgroup (K ⊔ S : Subgroup G)).map (K ⊔ S).subtype = S)
    (hpar : ChapterB.IsMinimalParabolicOver P ⊤) :
    Nonempty (ResidualBlockProduct (K ⊔ S : Subgroup G) P) := by
  obtain ⟨F,hn,hb,hg,hc,hi,ht,hm⟩ := ChapterC.RankOne.ChiProduct.residual_chiZero_orbit_of_characteristic_exclusion
    hsqtk hf P hpar
    (characteristic_exclusion_transport P hP (characteristic_exclusion S K hpush))
  exact ⟨⟨F,hn,hb,hg,hc,hi,ht,hm⟩⟩

theorem local_block_of_characteristic_obstruction
    (S K : Subgroup G) (hlocal : K ∈ Chapter1.L G S)
    (hn : S ≤ normalizer (K : Set G))
    (hpush : CharacteristicNormalizerObstruction S K)
    (hsqtk : IsSQTK KnownSimple.IsKnownSimple (K ⊔ S : Subgroup G))
    (hf : generalizedFitting (K ⊔ S : Subgroup G) = pCore 2 (K ⊔ S : Subgroup G))
    (hpar : ∀ P : Sylow 2 (K ⊔ S : Subgroup G),
      (P : Subgroup (K ⊔ S : Subgroup G)).map (K ⊔ S).subtype = S →
      ChapterB.IsMinimalParabolicOver P ⊤) :
    ChapterC.IsChiZeroBlockIn (K.subgroupOf (K ⊔ S)) := by
  obtain ⟨P,hP⟩ := hlocal.2.1
  obtain ⟨b⟩ := residual_product_of_characteristic_obstruction S K hpush hsqtk hf P hP (hpar P hP)
  exact b.block _ (RankOneBorel.Replacement.local_mem_factors S K hlocal hn P b)

theorem short_of_characteristic_obstruction
    (S K : Subgroup G) (hlocal : K ∈ Chapter1.L G S)
    (hn : S ≤ normalizer (K : Set G))
    (hpush : CharacteristicNormalizerObstruction S K)
    (hsqtk : IsSQTK KnownSimple.IsKnownSimple (K ⊔ S : Subgroup G))
    (hf : generalizedFitting (K ⊔ S : Subgroup G) = pCore 2 (K ⊔ S : Subgroup G))
    (hpar : ∀ P : Sylow 2 (K ⊔ S : Subgroup G),
      (P : Subgroup (K ⊔ S : Subgroup G)).map (K ⊔ S).subtype = S →
      ChapterB.IsMinimalParabolicOver P ⊤) : ChapterC.IsShort K :=
  (local_block_of_characteristic_obstruction S K hlocal hn hpush hsqtk hf hpar).1.short.of_mulEquiv
    (subgroupOfEquivOfLe le_sup_left)

private theorem not_alternating_three {H : Type*} [Group H] [Group.IsPerfect H] :
    ¬ ChapterC.IsAlternatingBlock H 3 := by
  intro h
  obtain ⟨e⟩ := h.2.2.quotient_iso
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : Group.IsPerfect (alternatingGroup (Fin 3)) :=
    Group.IsPerfect.ofSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact Group.IsPerfect.not_isMulCommutative (alternatingGroup (Fin 3))
    (alternatingGroup.isMulCommutative_of_card_le_three (by simp))

theorem block_alternatives_of_characteristic_obstruction
    (S K : Subgroup G) (hlocal : K ∈ Chapter1.L G S)
    (hn : S ≤ normalizer (K : Set G))
    (hpush : CharacteristicNormalizerObstruction S K)
    (hsqtk : IsSQTK KnownSimple.IsKnownSimple (K ⊔ S : Subgroup G))
    (hf : generalizedFitting (K ⊔ S : Subgroup G) = pCore 2 (K ⊔ S : Subgroup G))
    (hpar : ∀ P : Sylow 2 (K ⊔ S : Subgroup G),
      (P : Subgroup (K ⊔ S : Subgroup G)).map (K ⊔ S).subtype = S →
      ChapterB.IsMinimalParabolicOver P ⊤) :
    ChapterC.IsBlock (K.subgroupOf (K ⊔ S)) ∧
      ((∃ n, ChapterC.IsL2EvenBlock K n) ∨ ChapterC.IsAlternatingBlock K 5) := by
  have hb := local_block_of_characteristic_obstruction S K hlocal hn hpush hsqtk hf hpar
  let e : K.subgroupOf (K ⊔ S) ≃* K := subgroupOfEquivOfLe le_sup_left
  refine ⟨hb.1,?_⟩
  rcases hb.2 with ⟨n,hn⟩ | hthree | hfive
  · exact Or.inl ⟨n,hn.of_mulEquiv e⟩
  · let := Chapter1.mem_L_isPerfect hlocal
    exact (not_alternating_three (hthree.of_mulEquiv e)).elim
  · exact Or.inr (hfive.of_mulEquiv e)

theorem false_of_moving_nonshort_source
    (T K : Subgroup G) (z v : G)
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hSK : Tv T v ≤ normalizer (K : Set G))
    (hm : ¬ K ≤ centralizer ({z} : Set G))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D)
    (hsqtk : IsSQTK KnownSimple.IsKnownSimple (K ⊔ Tv T v : Subgroup G))
    (hf : generalizedFitting (K ⊔ Tv T v : Subgroup G) = pCore 2 (K ⊔ Tv T v : Subgroup G))
    (hpar : ∀ P : Sylow 2 (K ⊔ Tv T v : Subgroup G),
      (P : Subgroup (K ⊔ Tv T v : Subgroup G)).map (K ⊔ Tv T v).subtype = Tv T v →
      ChapterB.IsMinimalParabolicOver P ⊤) (hn : ¬ ChapterC.IsShort K) : False :=
  hn (short_of_characteristic_obstruction (Tv T v) K hlocal.2 hSK (h16 K hlocal hSK hm) hsqtk hf hpar)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
