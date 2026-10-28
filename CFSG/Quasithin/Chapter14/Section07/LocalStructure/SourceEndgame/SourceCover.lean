module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.Generation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SixCoordinates
public import Theory.Representation.BinaryConjugationSection.Coinvariants

/-!
# From the original Sylow group to the Ru2 cover

The literal Sylow SP in K and the bound S'≤U prove [P,K]U=P by the
perfect central-cover obstruction. The original conjugation coordinates
then give module commutator generation with the same K→SL₂(4) marking.
The natural projection with fixed kernel is consequently a cover.
The final application constructs RuTwo, deriving its six-dimensional
indecomposable action and retaining both actual coordinate homomorphisms.

The source still has to supply K's perfectness, the genuine Sylow
identification, the natural P/E projection and fixed kernel of order four,
and the local equalities identifying P with O₂(H) and Z(T) with V₁.
No theorem here asserts those remaining parts of 14.7.71–74. In particular,
the native H/P action on P/U is supplied only after elementary abelianness
has been proved; a dimension count is never used to construct that action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.73–75, printed pp.1076–1078 (PDF pp.1093–1095).
-/

public section

open Subgroup Representation Representation.OneCohomology Representation.SL2FourNatural
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
open ChapterJ

variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [FiniteDimensional (ZMod 2) W] in
/-- The actual Sylow and derived-subgroup inputs make the original projection a cover. -/
theorem source_module_cover
    (H K P S U : Subgroup G) [Group.IsPerfect K]
    [(P.subgroupOf K).Normal] [(U.subgroupOf K).Normal]
    (hKH : K ≤ H) (hPK : P ≤ K) (hSK : S ≤ K)
    (qH : H →* S5) (σ : Representation (ZMod 2) S5 W)
    (d : BinaryConjugationSection H P U (σ.comp qH))
    (a : L2FourAction) (qK : K →* SL)
    (hmark : ∀ k : K, qH ⟨k, hKH k.property⟩ = alternatingActor a (qK k))
    (p : Representation.IntertwiningMap (σ.comp (alternatingActor a)) naturalRepresentation)
    (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed (σ.comp (alternatingActor a)))
    (hP : IsPGroup 2 P) (R : Sylow 2 K)
    (hR : (R : Subgroup K).map K.subtype = S ⊔ P)
    (hS : ⁅S, S⁆ ≤ U) : IsCover p := by
  have hgen := commutator_generation_of_source_sylow K P S U hPK hSK d.kernel_le hP R hR hS
  refine ⟨hp, hk, d.coinvariants_eq_top_of_group_generation K hKH
    (σ.comp (alternatingActor a)) qK ?_ ?_⟩
  · intro k w
    change σ (qH ⟨k, hKH k.property⟩) w = σ (alternatingActor a (qK k)) w
    rw [hmark]
  · rwa [commutator_comm]

/-- Construct Ru2 without assuming indecomposability or module commutator generation. -/
theorem exists_ruTwo_of_source_sylow
    (V : Subgroup G) (T : Sylow 2 G)
    (K S : Subgroup G) [Group.IsPerfect K]
    [(((centralizerOfSylowCenter T).pCoreIn 2).subgroupOf K).Normal]
    [((conjugateSpan (centralizerOfSylowCenter T) V).subgroupOf K).Normal]
    (hKH : K ≤ centralizerOfSylowCenter T)
    (hPK : (centralizerOfSylowCenter T).pCoreIn 2 ≤ K) (hSK : S ≤ K)
    (qH : centralizerOfSylowCenter T →* S5)
    (hq : Function.Surjective qH)
    (hqker : qH.ker = ((centralizerOfSylowCenter T).pCoreIn 2).subgroupOf
      (centralizerOfSylowCenter T))
    (a : L2FourAction)
    (dn : BinaryConjugationSection (centralizerOfSylowCenter T)
      (conjugateSpan (centralizerOfSylowCenter T) V) (sylowCenter T) (a.action.comp qH))
    (σ : Representation (ZMod 2) S5 W)
    (d : BinaryConjugationSection (centralizerOfSylowCenter T)
      ((centralizerOfSylowCenter T).pCoreIn 2)
      (conjugateSpan (centralizerOfSylowCenter T) V) (σ.comp qH))
    (qK : K →* SL)
    (hmark : ∀ k : K, qH ⟨k, hKH k.property⟩ = alternatingActor a (qK k))
    (p : Representation.IntertwiningMap (σ.comp (alternatingActor a)) naturalRepresentation)
    (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed (σ.comp (alternatingActor a)))
    (hcard : Nat.card p.toLinearMap.ker = 4)
    (R : Sylow 2 K)
    (hR : (R : Subgroup K).map K.subtype = S ⊔ (centralizerOfSylowCenter T).pCoreIn 2)
    (hS : ⁅S, S⁆ ≤ conjugateSpan (centralizerOfSylowCenter T) V) :
    Nonempty (RuTwo V T) := by
  have hc := source_module_cover (centralizerOfSylowCenter T) K _ S _ hKH hPK hSK
    qH σ d a qK hmark p hp hk (isPGroup_pCoreIn 2 _) R hR hS
  exact exists_ruTwo_of_natural_and_cover V T qH hq hqker a dn σ d p hp hk hc.2.2 hcard

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
