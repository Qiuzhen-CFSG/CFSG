module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic.Cover

/-!
# Transport of the G₂ residual action to the original central extension

Restrict the ambient action to its normal G₂(2)′ subgroup and transport
it through the supplied group and natural-quotient equivalences. Whole-module
commutator generation and the literal central kernel make this a perfect
central cover. The model calculation then gives generation by the original
normalized local actor. All Sylow intersections and subgroup images are kept;
there is no hypothesis that the ambient Sylow lies in the component.

Source: Aschbacher–Smith, 13.5.21(6), printed p.924 / PDF p.941.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open Atlas.G2.Natural Atlas.G2.Natural.BinaryPlane
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic
namespace Transport
variable {H V W : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite H] [FiniteDimensional (ZMod 2) V] in
private theorem coinvariants_range (ρ : Representation (ZMod 2) H V) (q : Actor →* H) :
    Coinvariants.ker (ρ.comp q) = subspaceCommutator ρ ⊤ q.range := by
  unfold Coinvariants.ker subspaceCommutator
  congr 1
  ext x
  constructor
  · rintro ⟨⟨g,v⟩,rfl⟩
    exact ⟨q g,⟨g,rfl⟩,v,trivial,rfl⟩
  · rintro ⟨g,⟨a,rfl⟩,v,_,rfl⟩
    exact ⟨(a,v),rfl⟩

/-- Transport the model residual calculation along the actual central
quotient. The original module is allowed to be a nonsplit central extension. -/
theorem local_generation (N L : Subgroup H) [N.Normal] (S : Sylow 2 H)
    (hLN : L ≤ N) (hn : (S : Subgroup H) ≤ normalizer (L : Set H))
    (hperfect : IsPPerfect 2 L) (hne : ¬ L ≤ (S : Subgroup H))
    (ρ : Representation (ZMod 2) H V) (τ : Representation (ZMod 2) H W)
    (p : V →ₗ[ZMod 2] W) (hp : Function.Surjective p)
    (hact : ∀ g v, p (ρ g v) = τ g (p v))
    (hcentral : p.ker ≤ fixedSpace ρ N)
    (hgen : subspaceCommutator ρ ⊤ N = ⊤)
    (f : N ≃* Actor) (e : W ≃ₗ[ZMod 2] Coefficients)
    (he : ∀ g : N, ∀ w, e (τ g.val w) = action (f g) (e w))
    (X : Submodule (ZMod 2) V) (hX : Nat.card X = 4)
    (hd : Disjoint X p.ker)
    (hi : L ⊔ (S : Subgroup H) ≤ subspaceStabilizer ρ X) :
    subspaceCommutator ρ ⊤ L = ⊤ := by
  let q : Actor →* H := N.subtype.comp f.symm.toMonoidHom
  let σ : Representation (ZMod 2) Actor V := ρ.comp q
  have hq : q.range = N := by
    change (N.subtype.comp f.symm.toMonoidHom).range = N
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr f.symm.surjective, ← MonoidHom.range_eq_map, N.range_subtype]
  let p' : V →ₗ[ZMod 2] Coefficients := e.toLinearMap.comp p
  have he' (a : Actor) (v : V) : p' (σ a v) = action a (p' v) := by
    change e (p (ρ (f.symm a).val v)) = action a (e (p v))
    rw [hact, he, f.apply_symm_apply]
  let c : σ.IntertwiningMap (OrthogonalCover.binaryNatural (ZMod 2)) :=
    p'.intertwiningMap_of_isIntertwiningMap _ _ he'
  have hc : OneCohomology.IsCover c := by
    refine ⟨e.surjective.comp hp, ?_, ?_⟩
    · intro v hv a
      change e (p v) = 0 at hv
      have hv' : p v = 0 := e.injective (hv.trans e.map_zero.symm)
      exact hcentral hv' (f.symm a)
    · rw [coinvariants_range, hq]
      exact hgen
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal N
  let Rn := R.mapSurjective (f := f.toMonoidHom) f.surjective
  let Ln := (L.subgroupOf N).map f.toMonoidHom
  have hLn : Ln.map q = L := by
    rw [map_map]
    have heq : q.comp f.toMonoidHom = N.subtype := by ext a; exact congrArg Subtype.val (f.symm_apply_apply a)
    rw [heq, map_subgroupOf_eq_of_le hLN]
  have hnorm : (Rn : Subgroup Actor) ≤ normalizer (Ln : Set Actor) := by
    apply le_trans _ (le_normalizer_map f.toMonoidHom)
    apply map_mono
    rw [hR, ← subgroupOf_normalizer_eq hLN]
    exact comap_mono hn
  have hperf : IsPPerfect 2 Ln := by
    have hiL : IsPPerfect 2 (L.subgroupOf N) := hperfect.of_surjective
      (subgroupOfEquivOfLe hLN).symm.toMonoidHom (subgroupOfEquivOfLe hLN).symm.surjective
    exact hiL.of_surjective (f.toMonoidHom.subgroupMap (L.subgroupOf N))
      (f.toMonoidHom.subgroupMap_surjective _)
  have hnot : ¬ Ln ≤ (Rn : Subgroup Actor) := by
    intro hle
    apply hne
    intro l hl
    have hmem := hle (mem_map_of_mem f.toMonoidHom (show (⟨l,hLN hl⟩ : N) ∈ L.subgroupOf N from hl))
    obtain ⟨r,hr,her⟩ := hmem
    have her' : r = ⟨l,hLN hl⟩ := f.injective her
    subst r
    have ht : (⟨l,hLN hl⟩ : N) ∈ (S : Subgroup H).subgroupOf N := by rwa [← hR]
    exact ht
  let Xq := X.map p
  let Xn := Xq.map e.toLinearMap
  have hXn : Nat.card Xn = 4 := by
    rw [← Nat.card_congr (Submodule.equivMapOfInjective e.toLinearMap e.injective Xq).toEquiv]
    exact (Geometry.card_map_of_disjoint p X hd).trans hX
  have hstable : Ln ⊔ (Rn : Subgroup Actor) ≤ subspaceStabilizer action Xn := by
    apply sup_le
    · rintro _ ⟨l,hl,rfl⟩
      apply (mem_subspaceStabilizer_equivariant (τ.comp N.subtype) action f e he Xq l).mp
      exact Geometry.image_stable ρ τ p hact X l.val (hi (mem_sup_left hl))
    · rintro _ ⟨r,hr,rfl⟩
      apply (mem_subspaceStabilizer_equivariant (τ.comp N.subtype) action f e he Xq r).mp
      have ht : r ∈ (S : Subgroup H).subgroupOf N := by rwa [← hR]
      exact Geometry.image_stable ρ τ p hact X r.val (hi (mem_sup_right ht))
  have hg := Cover.local_generates σ c hc Rn Ln hnorm hperf Xn hXn hstable hnot
  have htransfer := subspaceCommutator_map_embedding σ ρ q (LinearMap.id : V →ₗ[ZMod 2] V)
    (fun _ _ => rfl) Ln ⊤
  simpa only [Submodule.map_id, hLn, hg] using htransfer.symm
end Transport
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic
