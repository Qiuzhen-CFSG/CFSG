module
public import Theory.Representation.G2BinaryPlaneHyperplaneSpan
public import Theory.ElementaryAbelian.Quotient
public import Theory.Representation.G2BinaryPointQuotient
public import Theory.SpecificGroups.SymmetricFive.OuterFourIntersection

/-!
# Small permutation images of the binary G₂ point module

An invariant subspace of the natural point-parabolic module which leaves the
marked three-space contains that three-space: root displacements produce its
three basis vectors. The existing invariant interval then says that any such
subspace of order above eight is the marked hyperplane or the whole module.

An elementary image in S₅ has order at most four. If its kernel is invariant
under the point parabolic, the preceding geometry improves this bound to two
and gives kernel order 32 or 64. Simultaneous conjugation of the actor map and
module coordinates transports the result to any nonzero natural point.

The actual ambient two-core quotient is applied in Chapter13's
OriginalOddNormalizer.RudvalisModuleIntersection. This does not assume that
its kernel equals the kernel of the natural-action quotient.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612, using B.4.6.
The inherited natural model retains the attribution in LICENSES/ATLAS.txt.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Subgroup
open scoped IsMulCommutative
local notation "ρ" => Restricted.NaturalCoordinates.action F

/-- Leaving the three-space forces its whole root-displacement span. -/
theorem seed_le_of_point_invariant_not_le_seed (S : Submodule F W)
    (hS : ∀ a ∈ BinaryCore.secondParabolic, ∀ v ∈ S, ρ a v ∈ S)
    (hn : ¬ S ≤ seed) : seed ≤ S := by
  have hA : rootA (1:F) ∈ BinaryCore.secondParabolic :=
    unipotent_le_parabolic (subset_closure (by simp))
  have hB : rootB (1:F) ∈ BinaryCore.secondParabolic :=
    unipotent_le_parabolic (subset_closure (by simp))
  have hC : rootC (1:F) ∈ BinaryCore.secondParabolic :=
    unipotent_le_parabolic (subset_closure (by simp))
  have hD : rootD (1:F) ∈ BinaryCore.secondParabolic :=
    unipotent_le_parabolic (subset_closure (by simp))
  have hE : rootE (1:F) ∈ BinaryCore.secondParabolic := rootE_mem_parabolic _
  have hR : (weylR : Model F) ∈ BinaryCore.secondParabolic := weylR_mem_parabolic
  obtain ⟨v,hv,hnv⟩ := SetLike.not_le_iff_exists.mp hn
  have hd (a : Model F) (ha : a ∈ BinaryCore.secondParabolic) (w : W) (hw : w ∈ S) :
      ρ a w - w ∈ S := S.sub_mem (hS a ha w hw) hw
  have hh : (Pi.single 0 1 : W) ∈ S ∧ (Pi.single 1 1 : W) ∈ S := by
    by_cases h5 : v 5 = 0
    · have h34 : v 3 ≠ 0 ∨ v 4 ≠ 0 := by
        by_contra hh
        push Not at hh
        exact hnv ((mem_seed v).mpr ⟨hh.1,hh.2,h5⟩)
      have hc : (v 3 • Pi.single 1 1 + v 4 • Pi.single 2 1 : W) ∈ S := by
        convert hd _ hC v hv using 1
        ext i
        fin_cases i <;> simp [h5]
      rcases h34 with h3 | h4
      · have h3 : v 3 = 1 := ((by decide : ∀ a:F, a=0 ∨ a=1) _).resolve_left h3
        have h0 : (Pi.single 0 1 : W) ∈ S := by
          convert hd _ hB v hv using 1
          ext i
          fin_cases i <;> simp [h5,h3]
        refine ⟨h0,?_⟩
        by_cases h4 : v 4 = 0
        · simpa [h3,h4] using hc
        · have h4 : v 4 = 1 := ((by decide : ∀ a:F, a=0 ∨ a=1) _).resolve_left h4
          have hc' : (Pi.single 1 1 + Pi.single 2 1 : W) ∈ S := by simpa [h3,h4] using hc
          convert hd _ hE _ hc' using 1
          ext i
          fin_cases i <;> simp
      · have h4 : v 4 = 1 := ((by decide : ∀ a:F, a=0 ∨ a=1) _).resolve_left h4
        have h0 : (Pi.single 0 1 : W) ∈ S := by
          convert hd _ hA v hv using 1
          ext i
          fin_cases i <;> simp [h5,h4]
        refine ⟨h0,?_⟩
        convert hd _ hE _ hc using 1
        ext i
        fin_cases i <;> simp [h4]
    · have h5 : v 5 = 1 := ((by decide : ∀ a:F, a=0 ∨ a=1) _).resolve_left h5
      have hb : (v 3 • Pi.single 0 1 + Pi.single 2 1 : W) ∈ S := by
        convert hd _ hB v hv using 1
        ext i
        fin_cases i <;> simp [h5]
      have h0 : (Pi.single 0 1 : W) ∈ S := by
        convert hd _ hD _ hb using 1
        ext i
        fin_cases i <;> simp
      refine ⟨h0,?_⟩
      have ha : (v 4 • Pi.single 0 1 + Pi.single 1 1 : W) ∈ S := by
        convert hd _ hA v hv using 1
        ext i
        fin_cases i <;> simp [h5]
      simpa only [add_sub_cancel_left] using S.sub_mem ha (S.smul_mem (v 4) h0)
  have h2 : (Pi.single 2 1 : W) ∈ S := by
    convert hS _ hR _ hh.2 using 1
    ext i
    fin_cases i <;> simp
  intro w hw
  obtain ⟨h3,h4,h5⟩ := (mem_seed w).mp hw
  have he : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 + w 2 • Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp [h3,h4,h5]
  rw [he]
  exact S.add_mem (S.add_mem (S.smul_mem _ hh.1) (S.smul_mem _ hh.2)) (S.smul_mem _ h2)

/-- A point-invariant subspace of order above eight is the hyperplane or the whole module. -/
theorem large_point_invariant_subspace (S : Submodule F W)
    (hS : ∀ a ∈ BinaryCore.secondParabolic, ∀ v ∈ S, ρ a v ∈ S)
    (hc : 8 < Nat.card S) : S = hyperplane ∨ S = ⊤ := by
  have hs : seed ≤ S := seed_le_of_point_invariant_not_le_seed S hS (by
    intro hh
    have hb := Nat.card_le_card_of_injective (Submodule.inclusion hh) (Submodule.inclusion_injective hh)
    rw [card_seed] at hb
    omega)
  rcases point_invariant_interval S hs (fun a ha => hS a ha.1) with h | h | h
  · rw [h,card_seed] at hc
    omega
  · exact Or.inl h
  · exact Or.inr h
variable {E : Type*} [Group E] [IsElementaryAbelian 2 E]

/-- An invariant kernel excludes elementary four-group images in S₅. -/
theorem fivePoint_image_card_le_two
    (θ : Additive E ≃ₗ[F] W) (f : E →* Equiv.Perm (Fin 5))
    (hn : ∀ a ∈ BinaryCore.secondParabolic, ∀ x ∈ f.ker,
      Additive.toMul (θ.symm (ρ a (θ (Additive.ofMul x)))) ∈ f.ker) :
    (Nat.card f.ker = 32 ∨ Nat.card f.ker = 64) ∧ Nat.card f.range ≤ 2 := by
  let S : Submodule F W := (AddSubgroup.toZModSubmodule 2 f.ker.toAddSubgroup).map θ.toLinearMap
  have hm (v : W) : v ∈ S ↔ Additive.toMul (θ.symm v) ∈ f.ker := by
    constructor
    · rintro ⟨x,hx,rfl⟩
      change Additive.toMul (θ.symm (θ x)) ∈ f.ker
      rw [θ.symm_apply_apply]
      exact hx
    · intro hx
      exact ⟨θ.symm v,hx,θ.apply_symm_apply v⟩
  let d : f.ker ≃ S := {
    toFun := fun x => ⟨θ (Additive.ofMul x),⟨Additive.ofMul x,x.property,rfl⟩⟩
    invFun := fun v => ⟨Additive.toMul (θ.symm v), (hm v).mp v.property⟩
    left_inv := fun x => Subtype.ext (θ.symm_apply_apply (Additive.ofMul x))
    right_inv := fun v => Subtype.ext (θ.apply_symm_apply v) }
  have hE : Nat.card E = 64 := by
    rw [Nat.card_congr (Additive.ofMul : E ≃ Additive E),Nat.card_congr θ.toEquiv]
    simp
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨T,hT⟩ := (IsElementaryAbelian.isPGroup 2 f.range).exists_le_sylow
  have hsmall : Nat.card f.range ≤ 4 :=
    Theory.SpecificGroups.SymmetricFive.OuterFourIntersection.elementary_card_le_four T f.range hT
  have hmul : Nat.card f.ker * Nat.card f.range = 64 := by
    rw [← index_ker,f.ker.card_mul_index,hE]
  have hlarge : 8 < Nat.card S := by
    rw [←Nat.card_congr d]
    nlinarith
  have hi : ∀ a ∈ BinaryCore.secondParabolic, ∀ v ∈ S, ρ a v ∈ S := by
    intro a ha v hv
    apply (hm _).mpr
    have hh := hn a ha (Additive.toMul (θ.symm v)) ((hm v).mp hv)
    change Additive.toMul (θ.symm (ρ a (θ (θ.symm v)))) ∈ f.ker at hh
    rwa [θ.apply_symm_apply] at hh
  have hcases : Nat.card f.ker = 32 ∨ Nat.card f.ker = 64 := by
    rw [Nat.card_congr d]
    rcases large_point_invariant_subspace S hi hlarge with hh | hh
    · exact Or.inl (hh ▸ card_hyperplane)
    · right
      rw [hh]
      simp
  refine ⟨hcases,?_⟩
  rcases hcases with h | h <;> rw [h] at hmul <;> omega

variable {D : Type*} [Group D]

/-- Transport the bound through the actual point-stabilizer action and original module marking. -/
theorem fivePoint_image_card_le_two_of_point_action
    (a : D →* Model F) (ha : Function.Surjective a)
    (P : Subgroup D) (v : Natural.Space F) (hv : v ≠ 0)
    (hP : ∀ x, x ∈ P ↔ Natural.action F (a x) v = v)
    (α : D →* MulAut E) (e : Additive E ≃ₗ[F] Natural.Space F)
    (he : ∀ x u, e (Additive.ofMul (α x u)) = Natural.action F (a x) (e (Additive.ofMul u)))
    (k : E →* Equiv.Perm (Fin 5))
    (hk : ∀ x : P, ∀ u ∈ k.ker, α x u ∈ k.ker) :
    (Nat.card k.ker = 32 ∨ Nat.card k.ker = 64) ∧ Nat.card k.range ≤ 2 := by
  obtain ⟨g,b,hb,_,hbg⟩ := exists_point_parabolic_map a ha P v hv hP
  let t := LinearMap.GeneralLinearGroup.toLinearEquiv ((Natural.action F).asGroupHom g)
  let c := Restricted.NaturalCoordinates.equiv F
  let θ := (e.trans t).trans c
  have hθ (x : P) (u : E) : θ (Additive.ofMul (α x u)) = ρ (b x) (θ (Additive.ofMul u)) := by
    change c (Natural.action F g (e (Additive.ofMul (α x u)))) =
      ρ (b x) (c (Natural.action F g (e (Additive.ofMul u))))
    rw [he]
    have hc := LinearMap.congr_fun
      ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' (b x))
      (Natural.action F g (e (Additive.ofMul u)))
    change c (Natural.action F (b x) (Natural.action F g (e (Additive.ofMul u)))) =
      ρ (b x) (c (Natural.action F g (e (Additive.ofMul u)))) at hc
    rw [←hc]
    congr 1
    rw [hbg]
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  apply fivePoint_image_card_le_two θ k
  intro y hy u hu
  obtain ⟨x,hx⟩ := hb ⟨y,hy⟩
  have hh := hθ x u
  rw [hx] at hh
  have hident : Additive.toMul (θ.symm (ρ y (θ (Additive.ofMul u)))) = α x u := by
    rw [←hh,θ.symm_apply_apply]
    rfl
  rw [hident]
  exact hk x u hu

end Atlas.G2.Natural.BinaryPointFlag
