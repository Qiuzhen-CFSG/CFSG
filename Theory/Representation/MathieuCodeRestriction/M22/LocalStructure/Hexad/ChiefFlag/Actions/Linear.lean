module

public import Theory.Representation.BinaryTransvectionGroups.Duality
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.SubrepresentationLattice

/-!
# Linear transports for the hexad actions

Surjective intertwiners detect maximal invariant kernels. Inverse duality
carries the full radical of a subspace to the full radical of its annihilator,
including surjectivity on automorphisms, and respects an explicit module
marking. These supply the linear steps in Aschbacher--Smith H.16.4(1)--(3),
printed p.403, combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Representation
namespace MathieuCode.Hexad.ChiefFlag.Actions
variable {G H X Y : Type*} [Group G] [Group H]
  [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]

def linearAction (ρ : Representation (ZMod 2) G X) : G →* BinaryLinear.GL X :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) X).toMonoidHom.comp
    ρ.asGroupHom

theorem dual_equivariant (ρ : Representation (ZMod 2) G X)
    (σ : Representation (ZMod 2) H Y) (q : G →* H) (e : X ≃ₗ[ZMod 2] Y)
    (he : ∀ g v, e (ρ g v) = σ (q g) (e v)) (g : G)
    (f : Module.Dual (ZMod 2) X) :
    e.symm.dualMap (ρ.dual g f) = σ.dual (q g) (e.symm.dualMap f) := by
  ext w
  change f (ρ g⁻¹ (e.symm w)) = f (e.symm (σ (q g)⁻¹ w))
  congr 1
  apply e.injective
  simpa only [LinearEquiv.apply_symm_apply, map_inv] using he g⁻¹ (e.symm w)

theorem irreducible_transport (ρ : Representation (ZMod 2) G X)
    (σ : Representation (ZMod 2) H Y) (q : G →* H) (hq : Function.Surjective q)
    (e : X ≃ₗ[ZMod 2] Y) (he : ∀ g v, e (ρ g v) = σ (q g) (e v))
    (hi : IsIrreducible σ) : IsIrreducible ρ := by
  let : Nontrivial Y := Subrepresentation.irreducible_module_nontrivial σ
  let : Nontrivial X := e.toEquiv.nontrivial
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  let T : Subrepresentation σ := ⟨P.toSubmodule.map e.toLinearMap, by
    rintro g _ ⟨v, hv, rfl⟩
    obtain ⟨a, rfl⟩ := hq g
    exact ⟨ρ a v, P.apply_mem_toSubmodule a hv, he a v⟩⟩
  rcases eq_bot_or_eq_top T with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    intro v hv
    have : e v ∈ T := ⟨v, hv, rfl⟩
    rw [hb] at this
    exact e.map_eq_zero_iff.mp this
  · right
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm le_top
    intro v _
    have : e v ∈ T := by rw [ht]; trivial
    obtain ⟨w, hw, hew⟩ := this
    exact e.injective hew ▸ hw

/-- An intertwiner into an irreducible module has no proper invariant space
strictly above its kernel. -/
theorem eq_ker_or_top (ρ : Representation (ZMod 2) G X)
    (σ : Representation (ZMod 2) G Y) (f : X →ₗ[ZMod 2] Y)
    (he : ∀ g v, f (ρ g v) = σ g (f v))
    (hi : IsIrreducible σ) (P : Subrepresentation ρ) (hk : f.ker ≤ P.toSubmodule) :
    P.toSubmodule = f.ker ∨ P.toSubmodule = ⊤ := by
  let T : Subrepresentation σ := ⟨P.toSubmodule.map f, by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, P.apply_mem_toSubmodule g hv, he g v⟩⟩
  rcases eq_bot_or_eq_top T with hb | ht
  · left
    apply le_antisymm _ hk
    intro v hv
    have : f v ∈ T := ⟨v, hv, rfl⟩
    rw [hb] at this
    exact this
  · right
    have hc := congrArg (Submodule.comap f ∘ Subrepresentation.toSubmodule) ht
    change (P.toSubmodule.map f).comap f = (⊤ : Submodule (ZMod 2) Y).comap f at hc
    simpa only [Submodule.comap_map_eq, sup_eq_left.mpr hk, Submodule.comap_top] using hc

/-- Adjacent dimensions give a chief factor for any action. -/
theorem covBy_of_finrank [FiniteDimensional (ZMod 2) X]
    {ρ : Representation (ZMod 2) G X} {A B : Subrepresentation ρ}
    (hAB : A ≤ B) (hd : Module.finrank (ZMod 2) B.toSubmodule =
      Module.finrank (ZMod 2) A.toSubmodule + 1) : A ⋖ B := by
  refine ⟨lt_of_le_of_ne hAB ?_, ?_⟩
  · intro h
    rw [h] at hd
    omega
  · intro P hAP hPB
    have h1 := Submodule.finrank_lt_finrank_of_lt
      (show A.toSubmodule < P.toSubmodule from hAP)
    have h2 := Submodule.finrank_lt_finrank_of_lt
      (show P.toSubmodule < B.toSubmodule from hPB)
    omega

/-- Every automorphism of a finite-dimensional dual comes from the inverse dual. -/
theorem contragredient_surjective [FiniteDimensional (ZMod 2) X] :
    Function.Surjective (BinaryTransvectionGroups.contragredient (V := X)) := by
  intro g
  let e := Module.evalEquiv (ZMod 2) X
  refine ⟨(e.trans g.symm.dualMap).trans e.symm, ?_⟩
  ext f v
  change f (e.symm (g.dualMap (e v))) = g f v
  rw [Module.apply_evalEquiv_symm_apply]
  rfl

/-- The entire axis radical dualizes to the entire center radical. -/
theorem dual_radical [FiniteDimensional (ZMod 2) X] (P : Submodule (ZMod 2) X) :
    (BinaryLinear.radical P).map BinaryTransvectionGroups.contragredient =
      BinaryLinear.radical P.dualAnnihilator := by
  ext g
  obtain ⟨a, rfl⟩ := contragredient_surjective g
  rw [BinaryTransvectionGroups.contragredient_mem_radical_iff]
  constructor
  · rintro ⟨b, hb, he⟩
    exact BinaryTransvectionGroups.contragredient_injective he ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- Full inverse-dual action, transported by a specified linear equivalence. -/
theorem dualAction_full [FiniteDimensional (ZMod 2) X]
    (ρ : G →* BinaryLinear.GL X) (σ : G →* BinaryLinear.GL Y)
    (P : Submodule (ZMod 2) X) (e : Module.Dual (ZMod 2) X ≃ₗ[ZMod 2] Y)
    (he : ∀ g f, e (BinaryTransvectionGroups.contragredient (ρ g) f) = σ g (e f))
    (hfull : ρ.range = BinaryLinear.radical P) :
    σ.range = BinaryLinear.radical (P.dualAnnihilator.map e.toLinearMap) := by
  have hdual : (BinaryTransvectionGroups.dualAction ρ).range =
      BinaryLinear.radical P.dualAnnihilator := by
    rw [BinaryTransvectionGroups.dualAction_range, BinaryTransvectionGroups.dualGroup,
      hfull, dual_radical]
  ext t
  constructor
  · rintro ⟨g, rfl⟩
    have hg : BinaryTransvectionGroups.contragredient (ρ g) ∈
        BinaryLinear.radical P.dualAnnihilator := by
      rw [← hdual]
      exact ⟨g, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      exact (he g f).symm.trans (congrArg e (hg.1 f hf))
    · intro v
      obtain ⟨f, rfl⟩ := e.surjective v
      exact ⟨_, hg.2 f, (e.map_sub _ _).trans (congrArg (fun z => z - e f) (he g f))⟩
  · intro ht
    let a : BinaryLinear.GL (Module.Dual (ZMod 2) X) := (e.trans t).trans e.symm
    have ha : a ∈ BinaryLinear.radical P.dualAnnihilator := by
      refine ⟨?_, ?_⟩
      · intro f hf
        apply e.injective
        change e (e.symm (t (e f))) = e f
        rw [e.apply_symm_apply, ht.1 (e f) ⟨f, hf, rfl⟩]
      · intro f
        obtain ⟨b, hb, hbe⟩ := ht.2 (e f)
        have hab : a f - f = b := by
          apply e.injective
          change e (e.symm (t (e f)) - f) = e b
          rw [map_sub, e.apply_symm_apply]
          exact hbe.symm
        exact hab.symm ▸ hb
    rw [← hdual] at ha
    obtain ⟨g, hg⟩ := ha
    refine ⟨g, ?_⟩
    ext v
    obtain ⟨f, rfl⟩ := e.surjective v
    rw [← he]
    change e (BinaryTransvectionGroups.dualAction ρ g f) = t (e f)
    rw [hg]
    exact e.apply_symm_apply _

end MathieuCode.Hexad.ChiefFlag.Actions
