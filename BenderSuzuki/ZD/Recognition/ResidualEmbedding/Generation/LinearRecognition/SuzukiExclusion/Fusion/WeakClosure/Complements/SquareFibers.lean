module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Interfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Bounds
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Cardinality
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ElementaryBranch
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Borel
public import Theory.SpecificGroups.Suzuki.RootSquareFibers
public import Theory.ElementaryAbelian.Join

/-!
# Square fibers and exterior involutions in the source Suzuki Sylow group

The actual Borel marking transfers the matrix square-fiber identity to P.
The product T = PU then has square fibers modulo M°U. An involution
outside T fixes the resulting difference; its centralizer on M°U is M°.
Consequently it centralizes T modulo M°, and every element in its T-coset
has square in M°. The source omega inequality supplies such an involution.

Source: GLS4, Chapter 2, Lemma 14.7(b), `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

public theorem Context.borel_square_fiber (d : Context Z M z t m)
    {x y : G} (hx : x ∈ borelTwoCore M z t) (hy : y ∈ borelTwoCore M z t)
    (he : x ^ 2 = y ^ 2) : x⁻¹ * y ∈ closure (Z ∩ (M : Set G)) := by
  obtain ⟨f, _, hP, hA⟩ := d.borel_marking
  let φ := (residualGenerated M z t).subtype.comp f.toMonoidHom
  have hi : Function.Injective φ := Subtype.val_injective.comp f.injective
  obtain ⟨a, ha, rfl⟩ := hP.symm ▸ hx
  obtain ⟨b, hb, rfl⟩ := hP.symm ▸ hy
  have hs : (⟨a, ha⟩ : SuzukiRootSubgroup m) ^ 2 = ⟨b, hb⟩ ^ 2 :=
    Subtype.ext (hi ((map_pow φ a 2).trans (he.trans (map_pow φ b 2).symm)))
  have hc := (suzukiRootSubgroup_square_eq_iff m d.parameter_pos _ _).mp hs
  rw [suzukiRootSubgroup_omega_eq_center m d.parameter_pos] at hA
  have hcenter := mem_map_of_mem (SuzukiRootSubgroup m).subtype hc
  have hmap : ((center (SuzukiRootSubgroup m)).map
      (SuzukiRootSubgroup m).subtype).map φ = closure (Z ∩ (M : Set G)) := hA
  have hh := hmap.le (mem_map_of_mem φ hcenter)
  change φ (a⁻¹ * b) ∈ closure (Z ∩ (M : Set G)) at hh
  rw [map_mul, map_inv] at hh
  exact hh

public theorem Context.borel_square_mem (d : Context Z M z t m)
    {x : G} (hx : x ∈ borelTwoCore M z t) :
    x ^ 2 ∈ closure (Z ∩ (M : Set G)) := by
  obtain ⟨f, _, hP, hA⟩ := d.borel_marking
  obtain ⟨a, ha, rfl⟩ := hP.symm ▸ hx
  rw [suzukiRootSubgroup_omega_eq_center m d.parameter_pos] at hA
  rw [← hA]
  exact ⟨a ^ 2, ⟨(⟨a, ha⟩ : SuzukiRootSubgroup m) ^ 2,
    suzukiRootSubgroup_square_mem_center m d.parameter_pos _, rfl⟩, map_pow _ _ _⟩

public theorem Context.borel_square_surjective (d : Context Z M z t m)
    {a : G} (ha : a ∈ closure (Z ∩ (M : Set G))) :
    ∃ x ∈ borelTwoCore M z t, x ^ 2 = a := by
  obtain ⟨f, _, hP, hA⟩ := d.borel_marking
  let φ := (residualGenerated M z t).subtype.comp f.toMonoidHom
  rw [suzukiRootSubgroup_omega_eq_center m d.parameter_pos] at hA
  obtain ⟨_, ⟨c, hc, rfl⟩, rfl⟩ := hA.symm ▸ ha
  obtain ⟨x, hx⟩ := suzukiRootSubgroup_square_surjective m d.parameter_pos ⟨c, hc⟩
  refine ⟨φ x, hP ▸ mem_map_of_mem φ x.property, ?_⟩
  exact (map_pow φ (x : SuzukiMatrixGroup m) 2).symm.trans
    (congrArg φ (congrArg Subtype.val hx))

public theorem LocalGeometry.P_commute_U (g : LocalGeometry Z M z t m)
    {x u : G} (hx : x ∈ borelTwoCore M z t) (hu : u ∈ g.U) : Commute x u :=
  mem_centralizer_iff.mp (g.U_le_centralizer hu) x ((g.P_eq ▸ hx).2)

public theorem LocalGeometry.U_le_closure_centralizer (g : LocalGeometry Z M z t m) :
    g.U ≤ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
  intro u hu
  exact mem_centralizer_iff.mpr fun a ha => g.P_commute_U (g.closure_le_P ha) hu

public theorem Context.closure_sup_U_elementary (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    IsElementaryAbelian 2 ↥(closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) := by
  let := (d.closure_elementary_card g).1
  let := g.U_elementary
  exact IsElementaryAbelian.sup_of_le_centralizer g.U_le_closure_centralizer

public theorem Context.T_square_mem (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) {x : G} (hx : x ∈ g.T) :
    x ^ 2 ∈ closure (Z ∩ (M : Set G)) := by
  have hxprod : x ∈ (borelTwoCore M z t : Set G) * (g.U : Set G) := g.T_product ▸ hx
  obtain ⟨p, hp, u, hu, rfl⟩ := hxprod
  let := g.U_elementary
  rw [(g.P_commute_U hp hu).mul_pow, elemPow_eq_one_of_isElementaryAbelian u hu, mul_one]
  exact d.borel_square_mem hp

public theorem Context.T_square_fiber (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) {x y : G} (hx : x ∈ g.T) (hy : y ∈ g.T)
    (he : x ^ 2 = y ^ 2) : x⁻¹ * y ∈ closure (Z ∩ (M : Set G)) ⊔ g.U := by
  have hxprod : x ∈ (borelTwoCore M z t : Set G) * (g.U : Set G) := g.T_product ▸ hx
  obtain ⟨p, hp, u, hu, rfl⟩ := hxprod
  have hyprod : y ∈ (borelTwoCore M z t : Set G) * (g.U : Set G) := g.T_product ▸ hy
  obtain ⟨q, hq, v, hv, rfl⟩ := hyprod
  let := g.U_elementary
  rw [(g.P_commute_U hp hu).mul_pow, (g.P_commute_U hq hv).mul_pow,
    elemPow_eq_one_of_isElementaryAbelian u hu,
    elemPow_eq_one_of_isElementaryAbelian v hv, mul_one, mul_one] at he
  have hf := d.borel_square_fiber hp hq he
  have hc := (g.P_commute_U ((borelTwoCore M z t).mul_mem
    ((borelTwoCore M z t).inv_mem hp) hq) (g.U.inv_mem hu)).symm
  have heq : (p * u)⁻¹ * (q * v) = (p⁻¹ * q) * (u⁻¹ * v) := by
    calc
      _ = (u⁻¹ * (p⁻¹ * q)) * v := by group
      _ = _ := by rw [hc.eq, mul_assoc]
  rw [heq]
  exact mul_mem_sup hf (g.U.mul_mem (g.U.inv_mem hu) hv)

public theorem SylowGeometry.closure_commute (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) {a x : G} (ha : a ∈ closure (Z ∩ (M : Set G)))
    (hx : x ∈ g.S) : Commute a x := by
  obtain ⟨b, hb, rfl⟩ := s.S_center.symm ▸ ha
  exact (congrArg Subtype.val (mem_center_iff.mp hb ⟨x, hx⟩)).symm

public theorem SylowGeometry.S_le_closure_centralizer (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) : g.S ≤ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
  intro x hx
  exact mem_centralizer_iff.mpr fun a ha => s.closure_commute g ha hx

public theorem SylowGeometry.fixed_closure_sup_U (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) {a v : G} (ha : a ∈ g.S) (haT : a ∉ g.T)
    (hv : v ∈ closure (Z ∩ (M : Set G)) ⊔ g.U) (hc : Commute a v) :
    v ∈ closure (Z ∩ (M : Set G)) := by
  have hp : v ∈ (closure (Z ∩ (M : Set G)) : Set G) * (g.U : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _
      (g.U_le_closure_centralizer.trans (Subgroup.centralizer_le_normalizer _))]
    exact hv
  obtain ⟨b, hb, u, hu, rfl⟩ := hp
  have hbu := (s.closure_commute g hb ha).symm
  have hau : Commute a u := by simpa only [inv_mul_cancel_left] using hbu.inv_right.mul_right hc
  have hu1 : u = 1 := by
    by_contra hu1
    apply haT
    rw [← g.centralizer_U u hu hu1]
    exact ⟨s.S_le_closure_centralizer g ha,
      mem_centralizer_singleton_iff.mpr hau.eq⟩
  change b * u ∈ closure (Z ∩ (M : Set G))
  rw [hu1, mul_one]
  exact hb

/-- An involution outside T centralizes T modulo the distinguished closure. -/
public theorem Context.involution_commutator_T (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    {a : G} (ha : a ∈ g.S) (haT : a ∉ g.T) (ha2 : a ^ 2 = 1)
    {x : G} (hx : x ∈ g.T) : ⁅a, x⁆ ∈ closure (Z ∩ (M : Set G)) := by
  have hn : g.S ≤ normalizer (g.T : Set G) := by
    obtain ⟨V, hV⟩ := g.S_sylow
    rw [← hV]
    exact map_subtype_le _
  have hcT : MulAut.conj a x ∈ g.T := (mem_normalizer_iff.mp (hn ha) x).mp hx
  have hsq : x ^ 2 = (MulAut.conj a x) ^ 2 := by
    rw [← map_pow, MulAut.conj_apply,
      (s.closure_commute g (d.T_square_mem g hx) ha).symm.eq, mul_inv_cancel_right]
  let v := x⁻¹ * MulAut.conj a x
  have hv : v ∈ closure (Z ∩ (M : Set G)) ⊔ g.U :=
    d.T_square_fiber g hx hcT hsq
  let := d.closure_sup_U_elementary g
  have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv2)
  have haa : MulAut.conj a (MulAut.conj a x) = x := by
    change a * (a * x * a⁻¹) * a⁻¹ = x
    calc
      _ = (a * a) * x * (a * a)⁻¹ := by group
      _ = x := by rw [← pow_two, ha2]; simp only [one_mul, inv_one, mul_one]
  have hcv : MulAut.conj a v = v := by
    change MulAut.conj a (x⁻¹ * MulAut.conj a x) = v
    rw [map_mul, map_inv, haa, ← hvi]
    simp only [v, mul_inv_rev, inv_inv]
  have hva := s.fixed_closure_sup_U g ha haT hv
    (mul_inv_eq_iff_eq_mul.mp hcv)
  have hcx := (s.closure_commute g hva (g.T_lt_S.le hx)).symm
  have he : ⁅a, x⁆ = v := by
    calc
      _ = x * v * x⁻¹ := by dsimp [v]; simp only [commutatorElement_def]; group
      _ = v := by rw [hcx.eq, mul_inv_cancel_right]
  rw [he]
  exact hva

/-- Strict growth of Ω₁ supplies the literal involution used in Lemma 14.7(b). -/
public theorem LocalGeometry.exists_involution_of_omega_lt
    (g : LocalGeometry Z M z t m)
    (h : omegaOneAmbient g.T < omegaOneAmbient g.S) :
    ∃ a ∈ g.S, a ^ 2 = 1 ∧ a ∉ g.T := by
  by_contra hn
  have ht : omegaOneAmbient g.S ≤ omegaOneAmbient g.T := by
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro a ha ha2
    have haT : a ∈ g.T := by
      by_contra haT
      exact hn ⟨a, ha, ha2, haT⟩
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl a haT ha2
  exact h.not_ge ht

/-- Every coset of T containing an involution consists of square roots of M°. -/
public theorem Context.involution_coset_square_mem (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    {a x : G} (ha : a ∈ g.S) (haT : a ∉ g.T) (ha2 : a ^ 2 = 1)
    (hx : x ∈ g.T) : (x * a) ^ 2 ∈ closure (Z ∩ (M : Set G)) := by
  have hc := d.involution_commutator_T g s ha haT ha2 hx
  have hcx := (s.closure_commute g hc (g.T_lt_S.le hx)).symm
  have he : (x * a) ^ 2 = ⁅a, x⁆ * x ^ 2 := by
    calc
      _ = x * ⁅a, x⁆ * x * a ^ 2 := by simp only [commutatorElement_def, pow_two]; group
      _ = ⁅a, x⁆ * x ^ 2 := by rw [ha2, mul_one, hcx.eq, mul_assoc, ← pow_two]
  rw [he]
  exact (closure (Z ∩ (M : Set G))).mul_mem hc (d.T_square_mem g hx)


end BenderSuzuki.ZD.SuzukiExclusion
