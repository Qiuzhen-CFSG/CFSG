module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.MovingCover

/-!
The Sylow commutator dimension identifies the moving part with the orthogonal
cover. A fixed direct summand is allowed in the original module: its projection
has kernel disjoint from the whole commutator submodule.
-/

@[expose] public noncomputable section
open Representation Representation.OneCohomology
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
open Representation.SL2OrthogonalCover
variable {F W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- A full Sylow commutator identifies the moving part, without imposing
commutator generation on the entire original module. -/
theorem orthogonal_map_of_sylow_moved_dimension (n : ℕ) (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) (SL F) W)
    (p : ρ.IntertwiningMap (binaryNatural (F := F)))
    (hp : Function.Surjective p) (hk : p.toLinearMap.ker = fixed ρ)
    (hs : Coinvariants.ker ρ ⊔ fixed ρ = ⊤)
    (P : Sylow 2 (SL F))
    (hmove : Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp P.toSubgroup.subtype)) = 2 * n) :
    ∃ f : ρ.IntertwiningMap (binaryAction (F := F)),
      Function.Surjective f ∧ Disjoint f.toLinearMap.ker (Coinvariants.ker ρ) := by
  obtain ⟨σ,q,pC,hpC,hret,_,hq,hmap⟩ :=
    moving_cover_of_fixed_supplement ρ (binaryNatural (F := F)) p hp hk hs
  let A := Coinvariants.ker (ρ.comp P.toSubgroup.subtype)
  let B := Coinvariants.ker (σ.comp P.toSubgroup.subtype)
  have hAC : A ≤ Coinvariants.ker ρ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,w⟩,rfl⟩
    exact Coinvariants.sub_mem_ker g.val w
  let qA : A →ₗ[ZMod 2] B :=
    (q.toLinearMap.comp A.subtype).codRestrict B
      (fun w => (hmap P).le (Submodule.mem_map_of_mem w.property))
  have hqAi : Function.Injective qA := by
    intro a b he
    have he' : q a.val = q b.val := congrArg Subtype.val he
    have ha := hret ⟨a.val,hAC a.property⟩
    have hb := hret ⟨b.val,hAC b.property⟩
    rw [ha,hb] at he'
    exact Subtype.ext (congrArg (fun w : Coinvariants.ker ρ => w.val) he')
  have hqAs : Function.Surjective qA := by
    intro b
    have hb : b.val ∈ A.map q.toLinearMap := (hmap P).symm ▸ b.property
    obtain ⟨a,ha,he⟩ := hb
    exact ⟨⟨a,ha⟩,Subtype.ext he⟩
  have hd : Module.finrank (ZMod 2) B = 2 * n :=
    (LinearEquiv.ofBijective qA ⟨hqAi,hqAs⟩).finrank_eq.symm.trans hmove
  obtain ⟨e,he,_⟩ := orthogonal_equiv_of_sylow_moved_dimension n hn hF σ pC hpC P hd
  let f : ρ.IntertwiningMap (binaryAction (F := F)) :=
    (e.symm.toLinearMap.comp q.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g w
      apply e.injective
      change e (e.symm (q (ρ g w))) = e (binaryAction g (e.symm (q w)))
      rw [e.apply_symm_apply,he,e.apply_symm_apply]
      exact LinearMap.congr_fun (q.isIntertwining' g) w)
  refine ⟨f,e.symm.surjective.comp hq,?_⟩
  apply disjoint_iff_inf_le.mpr
  intro w hw
  have hz : q w = 0 := e.symm.injective (by
    simpa only [map_zero] using (show e.symm (q w) = 0 from hw.1))
  rw [hret ⟨w,hw.2⟩] at hz
  exact congrArg Subtype.val hz

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
