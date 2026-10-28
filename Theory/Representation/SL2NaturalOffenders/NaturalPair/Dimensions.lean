module
public import Theory.Representation.SL2NaturalOffenders.NaturalPair
/-!
# Fixed codimensions on the actual paired natural layer

The coordinate projections of a product Sylow subgroup are defining Sylows.
Its fixed space is the product of their natural fixed lines, so its binary
fixed codimension is twice the defining field degree. The same identity
holds under a literal normal-layer marking. Exact fixed-space inverse images
under a surjection preserve codimension without a splitting assumption.
This provides B.2.18(d) for Aschbacher–Smith B.6.10/E.2.3's paired branch.
-/
public section
open Subgroup Representation.BinaryOffender
namespace Representation.SL2NaturalOffenders
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "D" => NoStrong.Actor F
local notation "N" => NoStrong.natural (F := F)
private theorem natural_sylow_codim (P : Sylow 2 D) :
    fixedCodim N (P : Subgroup D) = Module.finrank (ZMod 2) F := by
  let Q := P.mapSurjective (f := (topEquiv (G := D)).symm.toMonoidHom)
    (topEquiv (G := D)).symm.surjective
  have hh := Ratios.sylowImage_fixedCodim (⊤ : Subgroup D) topEquiv N (fun _ _ => rfl) Q
  have he : (Q : Subgroup (⊤ : Subgroup D)).map (⊤ : Subgroup D).subtype = P := by
    change ((P : Subgroup D).map (topEquiv (G := D)).symm.toMonoidHom).map _ = _
    rw [Subgroup.map_map]
    exact Subgroup.map_id _
  rwa [he] at hh

theorem naturalPair_sylow_fixedCodim (P : Sylow 2 (D × D)) :
    fixedCodim (naturalPair (F := F)) (P : Subgroup (D × D)) =
      2 * Module.finrank (ZMod 2) F := by
  let Q := P.mapSurjective (f := MonoidHom.fst D D) (fun x => ⟨(x,1),rfl⟩)
  let R := P.mapSurjective (f := MonoidHom.snd D D) (fun x => ⟨(1,x),rfl⟩)
  have hfixed : fixedSpace (naturalPair (F := F)) (P : Subgroup (D × D)) =
      (fixedSpace N (Q : Subgroup D)).prod (fixedSpace N (R : Subgroup D)) := by
    ext v
    constructor
    · intro hv
      constructor
      · rintro ⟨a,ha⟩
        obtain ⟨x,hx,hxa⟩ := ha
        change N a v.1 = v.1
        rw [←hxa]
        exact congrArg Prod.fst (hv ⟨x,hx⟩)
      · rintro ⟨a,ha⟩
        obtain ⟨x,hx,hxa⟩ := ha
        change N a v.2 = v.2
        rw [←hxa]
        exact congrArg Prod.snd (hv ⟨x,hx⟩)
    · intro hv a
      exact Prod.ext (hv.1 ⟨a.val.1,mem_map_of_mem (MonoidHom.fst D D) a.property⟩)
        (hv.2 ⟨a.val.2,mem_map_of_mem (MonoidHom.snd D D) a.property⟩)
  have hc := fixedCodim_add_finrank (naturalPair (F := F)) (P : Subgroup (D × D))
  have hQ := fixedCodim_add_finrank N (Q : Subgroup D)
  have hR := fixedCodim_add_finrank N (R : Subgroup D)
  rw [natural_sylow_codim] at hQ hR
  let e : (fixedSpace N (Q : Subgroup D)).prod (fixedSpace N (R : Subgroup D)) ≃ₗ[ZMod 2]
      (fixedSpace N (Q : Subgroup D)) × (fixedSpace N (R : Subgroup D)) :=
    { toFun := fun v => (⟨v.val.1,v.property.1⟩,⟨v.val.2,v.property.2⟩)
      invFun := fun v => ⟨(v.1.val,v.2.val),v.1.property,v.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hd := e.finrank_eq
  rw [Module.finrank_prod] at hd
  rw [hfixed,hd,Module.finrank_prod] at hc
  omega

variable {H : Type*} [Group H] [Finite H]
theorem paired_sylowImage_fixedCodim (L : Subgroup H)
    (e : L ≃* D × D)
    (ρ : Representation (ZMod 2) H ((Fin 2 → F) × (Fin 2 → F)))
    (hnat : ∀ (g : L) v, ρ (g : H) v = naturalPair (F := F) (e g) v)
    (P : Sylow 2 L) :
    fixedCodim ρ ((P : Subgroup L).map L.subtype) = 2 * Module.finrank (ZMod 2) F := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : fixedSpace ρ ((P : Subgroup L).map L.subtype) =
      fixedSpace (naturalPair (F := F)) (Q : Subgroup (D × D)) := by
    ext v
    constructor
    · intro hv a
      obtain ⟨x,hx,hxa⟩ := a.property
      change naturalPair (F := F) (a : D × D) v = v
      rw [←hxa]
      change naturalPair (F := F) (e x) v = v
      exact (hnat x v).symm.trans (hv ⟨(x : H),mem_map_of_mem L.subtype hx⟩)
    · intro hv a
      obtain ⟨x,hx,hxa⟩ := a.property
      change ρ (a : H) v = v
      rw [←hxa]
      change ρ (x : H) v = v
      exact (hnat x v).trans (hv ⟨e x,mem_map_of_mem e.toMonoidHom hx⟩)
  unfold fixedCodim
  rw [he]
  exact naturalPair_sylow_fixedCodim Q

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
omit [Finite F] [Finite H] [FiniteDimensional (ZMod 2) V] in
theorem fixedCodim_eq_of_fixedSpace_comap
    (α : Representation (ZMod 2) H V)
    (ρ : Representation (ZMod 2) H ((Fin 2 → F) × (Fin 2 → F)))
    (f : V →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F))) (hf : Function.Surjective f)
    (A : Subgroup H) (he : fixedSpace α A = (fixedSpace ρ A).comap f) :
    fixedCodim α A = fixedCodim ρ A := by
  unfold fixedCodim
  rw [he]
  let g := (fixedSpace ρ A).mkQ.comp f
  have hg : Function.Surjective g := (fixedSpace ρ A).mkQ_surjective.comp hf
  have hker : g.ker = (fixedSpace ρ A).comap f := by
    rw [LinearMap.ker_comp,Submodule.ker_mkQ]
  rw [←hker]
  exact (g.quotKerEquivOfSurjective hg).finrank_eq
end Representation.SL2NaturalOffenders
