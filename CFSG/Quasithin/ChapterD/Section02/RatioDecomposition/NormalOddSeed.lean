module
public import Theory.Representation.BinaryOffender.NormalOddSeed
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Split

/-!
# The faithful moved action from a normal odd seed reduction

For normal P ≤ K and an ambient generating seed fixed by S, the factorization
K = P(K ∩ S) makes the odd moved module [V,P] complementary to C_V(K).
The literal K-action on [V,P] is therefore faithful and retains the ambient
cubic minimum and starred actors. If K is the original Jhat, its restricted
Jhat is the whole actor, giving the precise input for D.2.16. The odd subgroup
itself acts fully, so any subgroup containing it, in particular the Fitting
subgroup when the group-theoretic inclusion is known, also acts fully.

Source: Aschbacher--Smith 15.1.2, first paragraph, printed pp.1084--1085;
the retained action and actor maps are those used in D.2.16--D.2.17.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)

/-- The equivariance field identifies any literal factor representation with its restricted action. -/
theorem FactorData.representation_eq_side {H : Subgroup G} {U : Submodule (ZMod 2) V}
    (d : FactorData ρ H U) (hs : H ≤ subspaceStabilizer ρ U) :
    d.representation = side ρ H U hs := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro v
  exact Subtype.ext (d.equivariant h v)

/-- Normality of P makes its moved space invariant under every ambient subgroup. -/
theorem oddMoved_stable (K P : Subgroup G) [P.Normal] :
    K ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ P) :=
  subspaceCommutator_invariant_normalizer ρ
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) le_normalizer_of_normal

/-- The literal K-action on the ambient moved space [V,P]. -/
@[expose] def oddMovedAction (K P : Subgroup G) [P.Normal] :
    Representation (ZMod 2) K (subspaceCommutator ρ ⊤ P) :=
  side ρ K (subspaceCommutator ρ ⊤ P) (oddMoved_stable ρ K P)

/-- The action uses the original representation and the literal subgroup inclusion. -/
theorem oddMovedAction_apply (K P : Subgroup G) [P.Normal]
    (k : K) (v : subspaceCommutator ρ ⊤ P) :
    ((oddMovedAction ρ K P k v : subspaceCommutator ρ ⊤ P) : V) = ρ (k:G) (v:V) := rfl

/-- The odd actor moves the whole restricted module. -/
theorem oddMovedAction_odd_full (K P : Subgroup G) [P.Normal] [Finite P]
    (hPK : P ≤ K) (hodd : Odd (Nat.card P)) :
    subspaceCommutator (oddMovedAction ρ K P) ⊤ (P.subgroupOf K) = ⊤ := by
  let U := subspaceCommutator ρ ⊤ P
  apply Submodule.map_injective_of_injective U.subtype_injective
  have hm := subspaceCommutator_map_embedding (ρ.comp K.subtype) (oddMovedAction ρ K P)
    (MonoidHom.id K) U.subtype (fun _ _ => rfl) (P.subgroupOf K) ⊤
  have hfull := NormalOddSeed.odd_moved_self ρ P hodd
  change subspaceCommutator ρ U P = U at hfull
  simpa only [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id,
    subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hPK,hfull] using hm.symm


/-- Every actor containing P moves the whole module; this applies to the Fitting subgroup. -/
theorem oddMovedAction_full_of_le (K P : Subgroup G) [P.Normal] [Finite P]
    (hPK : P ≤ K) (hodd : Odd (Nat.card P)) (A : Subgroup K)
    (hPA : P.subgroupOf K ≤ A) :
    subspaceCommutator (oddMovedAction ρ K P) ⊤ A = ⊤ := by
  apply top_unique
  apply (oddMovedAction_odd_full ρ K P hPK hodd).ge.trans
  apply Submodule.span_mono
  rintro _ ⟨p,hp,v,hv,rfl⟩
  exact ⟨p,hPA hp,v,hv,rfl⟩

variable [Finite G]

/-- The fixed complement transfers ambient faithfulness to the K-action. -/
theorem oddMovedAction_faithful (hf : Function.Injective ρ)
    (K P S : Subgroup G) [K.Normal] [P.Normal]
    (hodd : Odd (Nat.card P)) (hKP : K = P ⊔ (K ⊓ S))
    (Z : Submodule (ZMod 2) V) (hZ : Z ≤ fixedSpace ρ S)
    (hgen : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    Function.Injective (oddMovedAction ρ K P) :=
  side_faithful ρ hf (oddMoved_stable ρ K P)
    (NormalOddSeed.isCompl_moved_fixed ρ K P S hodd hKP Z hZ hgen).sup_eq_top le_rfl

/-- The K-action has no unmoved summand. -/
theorem oddMovedAction_full (K P S : Subgroup G) [K.Normal] [P.Normal]
    (hodd : Odd (Nat.card P)) (hKP : K = P ⊔ (K ⊓ S))
    (Z : Submodule (ZMod 2) V) (hZ : Z ≤ fixedSpace ρ S)
    (hgen : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    subspaceCommutator (oddMovedAction ρ K P) ⊤ ⊤ = ⊤ :=
  side_full ρ (oddMoved_stable ρ K P)
    (NormalOddSeed.moved_self ρ K P S hodd hKP Z hZ hgen)

variable [FiniteDimensional (ZMod 2) V]

/-- The cubic minimum and starred actors are preserved through the actual subgroup map. -/
theorem oddMovedAction_transport (K P S : Subgroup G) [K.Normal] [P.Normal]
    (hodd : Odd (Nat.card P)) (hKP : K = P ⊔ (K ⊓ S))
    (Z : Submodule (ZMod 2) V) (hZ : Z ≤ fixedSpace ρ S)
    (hgen : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤)
    (hwit : ∃ A ∈ QhatStar ρ, A ≤ K) :
    cubicRatio (oddMovedAction ρ K P) = cubicRatio ρ ∧
    ∀ B : Subgroup K, B ∈ QhatStar (oddMovedAction ρ K P) ↔ B.map K.subtype ∈ QhatStar ρ :=
  side_transport ρ (oddMoved_stable ρ K P)
    (NormalOddSeed.isCompl_moved_fixed ρ K P S hodd hKP Z hZ hgen).sup_eq_top le_rfl hwit


/-- When K contains every original starred actor, its restricted family maps onto that family. -/
theorem oddMovedAction_star_image (K P S : Subgroup G) [K.Normal] [P.Normal]
    (hodd : Odd (Nat.card P)) (hKP : K = P ⊔ (K ⊓ S))
    (Z : Submodule (ZMod 2) V) (hZ : Z ≤ fixedSpace ρ S)
    (hgen : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤)
    (hstars : ∀ A ∈ QhatStar ρ, A ≤ K) (hne : (QhatStar ρ).Nonempty) :
    (Subgroup.map K.subtype) '' QhatStar (oddMovedAction ρ K P) = QhatStar ρ := by
  have hwit : ∃ A ∈ QhatStar ρ, A ≤ K := by
    obtain ⟨A,hA⟩ := hne
    exact ⟨A,hA,hstars A hA⟩
  have ht := (oddMovedAction_transport ρ K P S hodd hKP Z hZ hgen hwit).2
  ext A
  constructor
  · rintro ⟨B,hB,rfl⟩
    exact (ht B).mp hB
  · intro hA
    refine ⟨A.subgroupOf K,(ht _).mpr ?_,map_subgroupOf_eq_of_le (hstars A hA)⟩
    rwa [map_subgroupOf_eq_of_le (hstars A hA)]

/-- The normal odd seed reduction supplies all the literal D.2.16 input data on Jhat. -/
@[expose] def normalOddFactorData (hf : Function.Injective ρ)
    (K P S : Subgroup G) [K.Normal] [P.Normal]
    (hodd : Odd (Nat.card P)) (hKP : K = P ⊔ (K ⊓ S))
    (Z : Submodule (ZMod 2) V) (hZ : Z ≤ fixedSpace ρ S)
    (hgen : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤)
    (hK : K = Jhat ρ) (hne : (QhatStar ρ).Nonempty) :
    FactorData ρ K (subspaceCommutator ρ ⊤ P) := by
  have hAK (A : Subgroup G) (hA : A ∈ QhatStar ρ) : A ≤ K := hK.symm ▸ le_sSup hA
  have hwit : ∃ A ∈ QhatStar ρ, A ≤ K := by
    obtain ⟨A,hA⟩ := hne
    exact ⟨A,hA,hAK A hA⟩
  have ht := oddMovedAction_transport ρ K P S hodd hKP Z hZ hgen hwit
  have hratio := ht.1
  have hstars := ht.2
  have hJ : Jhat (oddMovedAction ρ K P) = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    apply le_antisymm (map_subtype_le _)
    apply hK.le.trans
    apply sSup_le
    intro A hA
    have hA' : A.subgroupOf K ∈ QhatStar (oddMovedAction ρ K P) := by
      apply (hstars _).mpr
      rwa [map_subgroupOf_eq_of_le (hAK A hA)]
    have hm := Subgroup.map_mono (le_sSup hA') (f := K.subtype)
    simpa only [Jhat,map_subgroupOf_eq_of_le (hAK A hA)] using hm
  exact ⟨oddMovedAction ρ K P,fun _ _ => rfl,
    oddMovedAction_faithful ρ hf K P S hodd hKP Z hZ hgen,hJ,
    oddMovedAction_full ρ K P S hodd hKP Z hZ hgen,
    NormalOddSeed.moved_eq ρ K P S hKP Z hZ hgen,
    (NormalOddSeed.isCompl_moved_fixed ρ K P S hodd hKP Z hZ hgen).sup_eq_top,
    hratio,hstars⟩

/-- The constructed factor keeps the specified K-action on [V,P], independently of its proof fields. -/
theorem normalOddFactorData_representation (hf : Function.Injective ρ)
    (K P S : Subgroup G) [K.Normal] [P.Normal]
    (hodd : Odd (Nat.card P)) (hKP : K = P ⊔ (K ⊓ S))
    (Z : Submodule (ZMod 2) V) (hZ : Z ≤ fixedSpace ρ S)
    (hgen : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤)
    (hK : K = Jhat ρ) (hne : (QhatStar ρ).Nonempty) :
    (normalOddFactorData ρ hf K P S hodd hKP Z hZ hgen hK hne).representation =
      oddMovedAction ρ K P :=
  FactorData.representation_eq_side ρ _ (oddMoved_stable ρ K P)

end CFSG.Quasithin.ChapterD.RatioDecomposition
