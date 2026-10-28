module

public import Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive.Cubic
public import Theory.SpecificGroups.SymplecticFour.Binary.PlaneModel
public import Theory.GroupTheory.PrimeCyclicCoverage

/-!
# Retaining a cubic chosen in advance

The plane stabilizer normalizes the unique rank-two four-group and has order
48. Its Sylow-three conjugacy therefore aligns a prescribed normalizing cubic
with the cubic in the natural SL₂(4), without changing the literal four-group.
-/

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive
open Matrix Subgroup Representation.SL2FourNatural
open Representation.SL2FourNatural.BorelFactors
open Representation.SL2FourNatural.PointCommutator
open scoped Pointwise
local notation "Bit" => ZMod 2

private theorem conjugate_stabilizer (W X : Submodule Bit (Vector Bit))
    (g : Sp Bit) (hg : W.map (toLinear g).toLinearMap = X) :
    (stabilizer W).map (MulAut.conj g).toMonoidHom = stabilizer X := by
  have hmem (v : Vector Bit) : g • v ∈ X ↔ v ∈ W := by
    rw [←hg]
    constructor
    · rintro ⟨u,hu,he⟩
      exact (toLinear g).injective he ▸ hu
    · exact fun hv => ⟨v,hv,rfl⟩
  have hconj (s : Sp Bit) : g*s*g⁻¹ ∈ stabilizer X ↔ s ∈ stabilizer W := by
    rw [mem_stabilizer_iff,mem_stabilizer_iff]
    constructor
    · intro hs v hv
      have hh := hs (g • v) ((hmem v).mpr hv)
      simp only [mul_smul,inv_smul_smul] at hh
      exact (hmem (s • v)).mp hh
    · intro hs v hv
      have hw : g⁻¹ • v ∈ W := (hmem _).mp (by simpa using hv)
      have hh := (hmem _).mpr (hs _ hw)
      simpa only [mul_smul] using hh
  ext s
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (hconj a).mpr ha
  · intro hs
    refine ⟨g⁻¹*s*g, ?_, ?_⟩
    · apply (hconj _).mp
      have he : g*(g⁻¹*s*g)*g⁻¹ = s := by group
      rw [he]
      exact hs
    · change g*(g⁻¹*s*g)*g⁻¹=s
      group

/-- The actual isotropic binary plane stabilizer has order 48. -/
public theorem card_plane_stabilizer
    (W : Submodule Bit (Vector Bit)) (hW : Module.finrank Bit W = 2)
    (hiW : ∀ x ∈ W, ∀ y ∈ W, form Bit x y = 0) :
    Nat.card (stabilizer W) = 48 := by
  obtain ⟨g,hg⟩ := exists_plane_conjugator W (plane Bit) hW (finrank_plane (F := Bit))
    hiW (fun x hx y hy => plane_isotropic x y hx hy)
  have he := conjugate_stabilizer W (plane Bit) g hg
  have hc := Subgroup.card_map_of_injective (K := stabilizer W)
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [he] at hc
  rw [←hc]
  change Nat.card (planeParabolic (F := Bit)) = 48
  rw [Nat.card_congr planeParabolicZModEquivProd.toEquiv]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm]

/-- The plane stabilizer and the normalizer of its rank-two four-group are
the same literal subgroup of Sp₄(2). -/
public theorem normalizer_eq_plane_stabilizer
    (R : Subgroup (Sp Bit)) (W : Submodule Bit (Vector Bit))
    (hR : Nat.card R = 4) (hW : Module.finrank Bit W = 2)
    (hiW : ∀ x ∈ W, ∀ y ∈ W, form Bit x y = 0)
    (hfR : ∀ r ∈ R, r ≠ 1 → ∀ v : Vector Bit, r • v = v ↔ v ∈ W) :
    Subgroup.normalizer (R : Set (Sp Bit)) = stabilizer W := by
  apply le_antisymm
  · intro g hg
    apply (mem_stabilizer_iff W g).mpr
    have hn : R ≠ ⊥ := by
      intro he
      have hh := Subgroup.card_eq_one.mpr he
      omega
    obtain ⟨r,hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
    have hr1' : r.val ≠ 1 := fun he => hr1 (Subtype.ext he)
    have hc : g⁻¹*r.val*g ∈ R :=
      (Subgroup.mem_normalizer_iff''.mp hg r.val).mp r.property
    have hc1 : g⁻¹*r.val*g ≠ 1 := by
      intro he
      apply hr1'
      have hh := congrArg (MulAut.conj g) he
      simpa [MulAut.conj_apply,mul_assoc] using hh
    intro v hv
    apply (hfR r.val r.property hr1' _).mp
    have hh := congrArg (fun w : Vector Bit => g • w)
      ((hfR _ hc hc1 v).mpr hv)
    simpa only [mul_smul,smul_inv_smul] using hh
  · intro g hg
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_common_fixed_plane W hW hiW _ R
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,hR]) hR ?_ hfR
    rintro r ⟨a,ha,rfl⟩ hr v
    have ha1 : a ≠ 1 := by intro he; simp [he] at hr
    have hgi := (mem_stabilizer_iff W g⁻¹).mp ((stabilizer W).inv_mem hg)
    have hgf := (mem_stabilizer_iff W g).mp hg
    change ((g*a*g⁻¹) • v = v) ↔ v ∈ W
    constructor
    · intro hh
      have hx := congrArg (fun w : Vector Bit => g⁻¹ • w) hh
      have hw : g⁻¹ • v ∈ W := (hfR a ha ha1 _).mp (by
        simpa only [mul_smul,inv_smul_smul] using hx)
      simpa only [smul_inv_smul] using hgf _ hw
    · intro hv
      have hh := congrArg (fun w : Vector Bit => g • w)
        ((hfR a ha ha1 _).mpr (hgi v hv))
      simpa only [mul_smul,smul_inv_smul] using hh

/-- A prescribed cubic normalizing the rank-two four-group belongs to a
faithful natural SL₂(4) containing that exact four-group. -/
public theorem exists_marked_embedding_containing_cubic
    (R : Subgroup (Sp Bit)) (W : Submodule Bit (Vector Bit))
    (hR : Nat.card R = 4) (hW : Module.finrank Bit W = 2)
    (hiW : ∀ x ∈ W, ∀ y ∈ W, form Bit x y = 0)
    (hfR : ∀ r ∈ R, r ≠ 1 → ∀ v : Vector Bit, r • v = v ↔ v ∈ W)
    (t : Sp Bit) (ht : orderOf t = 3)
    (htR : t ∈ Subgroup.normalizer (R : Set (Sp Bit))) :
    ∃ e : V ≃ₗ[Bit] Vector Bit, ∃ ι : SL →* Sp Bit,
      Function.Injective ι ∧ (∀ g v, ι g • e v = e (action g v)) ∧
      U0.map ι = R ∧ upperFixed.map e.toLinearMap = W ∧ t ∈ ι.range := by
  obtain ⟨e,ι,hι,hm,hRι,hWι,hc,hcN,_,hcW,_⟩ :=
    exists_marked_embedding_with_cubic R W hR hW hiW hfR
  let N := stabilizer W
  have hnorm := normalizer_eq_plane_stabilizer R W hR hW hiW hfR
  have htN : t ∈ N := by
    change t ∈ stabilizer W
    rwa [←hnorm]
  have hcN' : ι cubic ∈ N := (mem_stabilizer_iff W _).mpr hcW
  let a : N := ⟨ι cubic,hcN'⟩
  let b : N := ⟨t,htN⟩
  have ha : orderOf a = 3 := (Subgroup.orderOf_coe a).symm.trans hc
  have hb : orderOf b = 3 := (Subgroup.orderOf_coe b).symm.trans ht
  obtain ⟨n,g,hg⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    (by decide : Nat.Prime 3) (by rw [card_plane_stabilizer W hW hiW]; decide) ha hb
  let ι' := (MulAut.conj g.val).toMonoidHom.comp ι
  let e' := e.trans (toLinear g.val)
  have hgR : g.val ∈ Subgroup.normalizer (R : Set (Sp Bit)) := by
    rw [hnorm]
    exact g.property
  have hge : R.map (MulAut.conj g.val).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgR
  refine ⟨e',ι',(MulAut.conj g.val).injective.comp hι,?_,?_,?_,?_⟩
  · intro x v
    change (g.val*ι x*g.val⁻¹) • (g.val • e v) = g.val • e (action x v)
    simp only [mul_smul,inv_smul_smul,hm]
  · change U0.map ((MulAut.conj g.val).toMonoidHom.comp ι) = R
    rw [←Subgroup.map_map,hRι,hge]
  · change upperFixed.map ((toLinear g.val).toLinearMap.comp e.toLinearMap) = W
    rw [Submodule.map_comp,hWι]
    exact g.property
  · refine ⟨cubic^n, ?_⟩
    have he := congrArg Subtype.val hg
    change t = g.val * ((ι cubic)^n) * g.val⁻¹ at he
    change g.val * ι (cubic^n) * g.val⁻¹ = t
    simpa only [map_pow] using he.symm

end Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive
