module
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.PureLong.Coordinates
public import Theory.ElementaryAbelian.Basic
import all Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.InvolutionConjugacy

/-!
# Simultaneous fusion of pure-long elementary subgroups of even G₂

Let B be an elementary abelian two-subgroup of the actual split-octonion
G₂ model, all of whose nonidentity elements are long-root elements. One
conjugator places the whole subgroup inside the actual A/B root plane.

Place B in the six-root Sylow subgroup. The proved long-root equations give
`f=0`, `d²=ec`, `c²=bd`, and `be=cd`. If every E coordinate vanishes, B is
already in the A/B plane. Otherwise one F-root conjugation sends an anchor
with nonzero E coordinate into the A/E plane. Commutation with that anchor
forces the B coordinate of every subgroup element to vanish; the long-root
equations then kill its C and D coordinates. The short Weyl reflection sends
the entire A/E plane into A/B. The final order bound uses this literal plane.

The internal import reuses the existing signed root conjugation identity in
this involution-geometry family; no class table or simultaneous-placement
hypothesis is introduced. Source: Aschbacher–Smith B.4.6(11), printed p.89,
and the pure-long exclusion in B.4.6(13), printed p.90. The imported root
formulas retain the ATLAS attribution in LICENSES/ATLAS-CITATION.cff.
-/

namespace Atlas.G2.EvenInvolutionGeometry.PureLong
open Subgroup LieParabolicSetup
open scoped IsMulCommutative
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] [Finite F] in
private theorem pure_conj (B : Subgroup (Model F))
    (hp : ∀ b ∈ B, b ≠ 1 → ShortRootProducts.IsLongRootElement b) (g : Model F) :
    ∀ b ∈ B.map (MulAut.conj g).toMonoidHom,
      b ≠ 1 → ShortRootProducts.IsLongRootElement b := by
  rintro _ ⟨b,hb,rfl⟩ hn
  apply long_conj g (hp b hb ?_)
  intro h
  exact hn (by simp [h])

private theorem pure_coordinates (B : Subgroup (Model F))
    (hp : ∀ b ∈ B, b ≠ 1 → ShortRootProducts.IsLongRootElement b)
    (t : Fin 6 → F) (ht : unipotentProduct t ∈ B) :
    t 5 = 0 ∧ (t 3)^2 = t 4*t 2 ∧ (t 2)^2 = t 1*t 3 ∧ t 1*t 4 = t 2*t 3 := by
  apply unipotent_one_or_long_coordinates
  by_cases he : unipotentProduct t = 1
  · exact Or.inl he
  · exact Or.inr (hp _ ht he)

omit [Finite F] in
private theorem normalize_anchor (t : Fin 6 → F)
    (ht : t 5 = 0 ∧ (t 3)^2 = t 4*t 2 ∧ (t 2)^2 = t 1*t 3 ∧ t 1*t 4 = t 2*t 3)
    (he : t 4 ≠ 0) :
    ∃ a : F, MulAut.conj (rootF (t 3/t 4)) (unipotentProduct t) =
      unipotentProduct ![a,0,0,0,t 4,0] := by
  let z := t 3/t 4
  have hz : t 4*z = t 3 := by dsimp [z]; field_simp
  have hc : t 4*z^2 = t 2 := by
    apply mul_left_cancel₀ he
    calc
      t 4*(t 4*z^2) = (t 4*z)^2 := by ring
      _ = (t 3)^2 := by rw [hz]
      _ = t 4*t 2 := ht.2.1
  have hb : t 1 = t 2*z := by
    apply mul_right_cancel₀ he
    calc
      t 1*t 4 = t 2*t 3 := ht.2.2.2
      _ = t 2*(t 4*z) := by rw [hz]
      _ = (t 2*z)*t 4 := by ring
  have hvec : t = ![t 0,t 1,t 2,t 3,t 4,t 5] := by ext i; fin_cases i <;> rfl
  refine ⟨t 0+(t 3)^2*z+t 3*t 4*z^2+(t 4)^2*z^3, ?_⟩
  change MulAut.conj (rootF z) (unipotentProduct t) = _
  rw [show unipotentProduct t = unipotentProduct ![t 0,t 1,t 2,t 3,t 4,t 5] from
    congrArg unipotentProduct hvec, conjugate_F]
  congr 1
  ext i
  fin_cases i <;> simp [ht.1, hc, hz, CharTwo.add_self_eq_zero]
  rw [hb, ← hz]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

omit [Finite F] in
private theorem commuting_anchor_coordinates (a e : F) (he : e ≠ 0) (t : Fin 6 → F)
    (ht : t 5 = 0 ∧ (t 3)^2 = t 4*t 2 ∧ (t 2)^2 = t 1*t 3 ∧ t 1*t 4 = t 2*t 3)
    (hc : Commute (unipotentProduct ![a,0,0,0,e,0]) (unipotentProduct t)) :
    t 1 = 0 ∧ t 2 = 0 ∧ t 3 = 0 := by
  have hh := hc.eq
  rw [unipotentProduct_mul, unipotentProduct_mul] at hh
  have h0 := congrFun (unipotentProduct_injective hh) 0
  simp [unipotentProductParameters, ht.1, CharTwo.sub_eq_add, CharTwo.ofNat_eq_mod] at h0
  have hb : t 1*e = 0 := by linear_combination h0
  have hb' := (mul_eq_zero.mp hb).resolve_right he
  have hcc : (t 2)^2 = 0 := by rw [ht.2.2.1,hb',zero_mul]
  have hc' : t 2 = 0 := sq_eq_zero_iff.mp hcc
  have hdd : (t 3)^2 = 0 := by rw [ht.2.1,hc',mul_zero]
  exact ⟨hb',hc',sq_eq_zero_iff.mp hdd⟩

omit [Finite F] in
private theorem AE_conjugate_mem_longRootLocal (t : Fin 6 → F)
    (hb : t 1 = 0) (hc : t 2 = 0) (hd : t 3 = 0) (hf : t 5 = 0) :
    MulAut.conj weylS (unipotentProduct t) ∈ longRootLocal := by
  change weylS * unipotentProduct t * weylS⁻¹ ∈ longRootLocal
  rw [weylS_fiveRoot_conjugate _ hf]
  refine ⟨Multiplicative.ofAdd (t 0,t 4), ?_⟩
  simp [longRootHom, unipotentProduct, hb,hc,hd]

private theorem unipotent_pure_fusion (B : Subgroup (Model F)) [IsElementaryAbelian 2 B]
    (hBU : B ≤ unipotent)
    (hp : ∀ b ∈ B, b ≠ 1 → ShortRootProducts.IsLongRootElement b) :
    ∃ g : Model F, B.map (MulAut.conj g).toMonoidHom ≤ longRootLocal := by
  by_cases he : ∃ t : Fin 6 → F, unipotentProduct t ∈ B ∧ t 4 ≠ 0
  · obtain ⟨t,htB,he⟩ := he
    let g := rootF (t 3/t 4)
    let C := B.map (MulAut.conj g).toMonoidHom
    let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
    have hgU : g ∈ unipotent := by
      simpa [g,unipotentProduct] using unipotentProduct_mem ![0,0,0,0,0,t 3/t 4]
    have hCU : C ≤ unipotent := by
      rintro _ ⟨b,hb,rfl⟩
      change g*b*g⁻¹ ∈ unipotent
      exact unipotent.mul_mem (unipotent.mul_mem hgU (hBU hb)) (unipotent.inv_mem hgU)
    have hpC := pure_conj B hp g
    obtain ⟨a,ha⟩ := normalize_anchor t (pure_coordinates B hp t htB) he
    have haC : unipotentProduct ![a,0,0,0,t 4,0] ∈ C :=
      ha ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom htB
    refine ⟨weylS*g, ?_⟩
    rintro _ ⟨b,hb,rfl⟩
    change MulAut.conj (weylS*g) b ∈ longRootLocal
    rw [map_mul, MulAut.mul_apply]
    have hbC : MulAut.conj g b ∈ C := mem_map_of_mem _ hb
    have hbU := hCU hbC
    rw [unipotent_eq_range] at hbU
    obtain ⟨u,hu⟩ := hbU
    have huC : unipotentProduct u ∈ C := hu.symm ▸ hbC
    have huc := pure_coordinates C hpC u huC
    have hcomm : Commute (unipotentProduct ![a,0,0,0,t 4,0]) (unipotentProduct u) := by
      change _ * _ = _ * _
      exact congrArg Subtype.val (mul_comm
        (⟨_,haC⟩ : C) (⟨_,huC⟩ : C))
    obtain ⟨h1,h2,h3⟩ := commuting_anchor_coordinates a (t 4) he u huc hcomm
    rw [← hu]
    exact AE_conjugate_mem_longRootLocal u h1 h2 h3 huc.1
  · refine ⟨1, ?_⟩
    intro b hb
    have hbB : b ∈ B := by simpa using hb
    have hbU := hBU hbB
    rw [unipotent_eq_range] at hbU
    obtain ⟨t,rfl⟩ := hbU
    have htc := pure_coordinates B hp t hbB
    have h4 : t 4 = 0 := by by_contra h; exact he ⟨t,hbB,h⟩
    have hdd : (t 3)^2 = 0 := by rw [htc.2.1,h4,zero_mul]
    have h3 : t 3 = 0 := sq_eq_zero_iff.mp hdd
    have hcc : (t 2)^2 = 0 := by rw [htc.2.2.1,h3,mul_zero]
    have h2 : t 2 = 0 := sq_eq_zero_iff.mp hcc
    refine ⟨Multiplicative.ofAdd (t 0,t 1), ?_⟩
    simp [longRootHom,unipotentProduct,h2,h3,h4,htc.1]

public theorem exists_map_le_longRootLocal (B : Subgroup (Model F))
    (hB : IsElementaryAbelian 2 B)
    (hp : ∀ b ∈ B, b ≠ 1 → ShortRootProducts.IsLongRootElement b) :
    ∃ g : Model F, B.map (MulAut.conj g).toMonoidHom ≤ longRootLocal := by
  let : IsElementaryAbelian 2 B := hB
  obtain ⟨S,hS⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq (Model F) (sylow (F := F)) S
  have hm : unipotent.map (MulAut.conj k).toMonoidHom = (S : Subgroup (Model F)) :=
    congrArg Sylow.toSubgroup hk
  let C := B.map (MulAut.conj k⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have hCU : C ≤ unipotent := by
    rintro _ ⟨b,hb,rfl⟩
    have hbS : b ∈ unipotent.map (MulAut.conj k).toMonoidHom := hm.symm ▸ hS hb
    obtain ⟨u,hu,rfl⟩ := hbS
    simpa [MulAut.conj_apply,mul_assoc] using hu
  obtain ⟨g,hg⟩ := unipotent_pure_fusion C hCU (pure_conj B hp k⁻¹)
  refine ⟨g*k⁻¹, ?_⟩
  rintro _ ⟨b,hb,rfl⟩
  change MulAut.conj (g*k⁻¹) b ∈ longRootLocal
  rw [map_mul,MulAut.mul_apply]
  exact hg (mem_map_of_mem _ (mem_map_of_mem (MulAut.conj k⁻¹).toMonoidHom hb))

public theorem exists_le_conjugate_longRootLocal (B : Subgroup (Model F))
    (hB : IsElementaryAbelian 2 B)
    (hp : ∀ b ∈ B, b ≠ 1 → ShortRootProducts.IsLongRootElement b) :
    ∃ g : Model F, B ≤ longRootLocal.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := exists_map_le_longRootLocal B hB hp
  refine ⟨g⁻¹, ?_⟩
  intro b hb
  refine ⟨MulAut.conj g b, hg (mem_map_of_mem _ hb), ?_⟩
  simp [MulAut.conj_apply,mul_assoc]

/-- A pure-long elementary subgroup has order at most the actual root-plane order. -/
public theorem card_le_field_square (B : Subgroup (Model F))
    (hB : IsElementaryAbelian 2 B)
    (hp : ∀ b ∈ B, b ≠ 1 → ShortRootProducts.IsLongRootElement b) :
    Nat.card B ≤ Nat.card F ^ 2 := by
  obtain ⟨g,hg⟩ := exists_map_le_longRootLocal B hB hp
  calc
    Nat.card B = Nat.card (B.map (MulAut.conj g).toMonoidHom) :=
      Nat.card_congr (B.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv
    _ ≤ Nat.card (longRootLocal (F := F)) :=
      Nat.card_le_card_of_injective (inclusion hg) (inclusion_injective hg)
    _ = Nat.card F ^ 2 := card_longRootLocal

end Atlas.G2.EvenInvolutionGeometry.PureLong
