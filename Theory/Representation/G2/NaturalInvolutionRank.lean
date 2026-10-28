module

public import Theory.Representation.G2.RestrictedModules.NaturalCoordinates
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic

/-!
# Natural G₂ involutions are not transvections

For the actual six-dimensional trace-zero octonion quotient, displacement rank
at most one makes every two-by-two coordinate minor vanish. Six minors of an
ordered unipotent product successively kill its parameters, starting with the
last root. Thus every nonidentity element of the concrete six-root subgroup
moves at least two dimensions. Sylow conjugacy applies this to every involution
of the full finite octonion automorphism group, including G₂(2).

An involution in characteristic two has square-zero displacement, so its image
lies in its kernel. Rank-nullity bounds its natural displacement rank by three.
The resulting interval supplies the natural no-transvection input in the actual
Frobenius pair in `HalfTensor.PairDisplacement.Inner`.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5,
manuscript pp.20,55–56. Root coordinates, their ordering, and the actual Sylow
subgroup are from the attributed ATLAS ports imported above; no new ATLAS
source is copied here.
-/

public noncomputable section
open Module Representation.BinaryOffender.NaturalTensor
open Atlas.G2.Restricted.NaturalCoordinates

namespace Atlas.G2.Natural.InvolutionRank
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem minors_vanish (D : Module.End F (Fin 6 → F))
    (h : finrank F D.range ≤ 1) (x y : Fin 6 → F) (i j : Fin 6) :
    D x i * D y j = D y i * D x j := by
  obtain ⟨u, hu⟩ := finrank_le_one_iff.mp h
  obtain ⟨a, ha⟩ := hu ⟨D x, x, rfl⟩
  obtain ⟨b, hb⟩ := hu ⟨D y, y, rfl⟩
  have ha' := congrArg Subtype.val ha
  have hb' := congrArg Subtype.val hb
  change a • (u : Fin 6 → F) = D x at ha'
  change b • (u : Fin 6 → F) = D y at hb'
  rw [← ha', ← hb']
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem product_eq_one_of_small_rank (t : Fin 6 → F)
    (h : operatorFixedCodim (Restricted.NaturalCoordinates.action F (unipotentProduct t)) ≤ 1) :
    unipotentProduct t = 1 := by
  have hm := minors_vanish (Restricted.NaturalCoordinates.action F (unipotentProduct t) - 1) h
  have hf : t 5 = 0 := by
    have hh := hm (Pi.single 1 1) (Pi.single 5 1) 0 4
    simpa [unipotentProduct, map_mul, Module.End.mul_apply] using hh
  have he : t 4 = 0 := by
    have hh := hm (Pi.single 2 1) (Pi.single 4 1) 1 3
    simpa [unipotentProduct, map_mul, Module.End.mul_apply, hf] using hh
  have hd : t 3 = 0 := by
    have hh := hm (Pi.single 2 1) (Pi.single 5 1) 0 3
    simpa [unipotentProduct, map_mul, Module.End.mul_apply, hf, he] using hh
  have hc : t 2 = 0 := by
    have hh := hm (Pi.single 3 1) (Pi.single 4 1) 1 2
    simpa [unipotentProduct, map_mul, Module.End.mul_apply, hf, he, hd] using hh
  have hb : t 1 = 0 := by
    have hh := hm (Pi.single 3 1) (Pi.single 5 1) 0 2
    simpa [unipotentProduct, map_mul, Module.End.mul_apply, hf, he, hd, hc] using hh
  have ha : t 0 = 0 := by
    have hh := hm (Pi.single 4 1) (Pi.single 5 1) 0 1
    simpa [unipotentProduct, map_mul, Module.End.mul_apply, hf, he, hd, hc, hb] using hh
  simp [unipotentProduct, ha, hb, hc, hd, he, hf]

/-- Every nonidentity element of the actual six-root subgroup moves at least two dimensions. -/
theorem two_le_operatorFixedCodim_of_mem_unipotent (g : Model F) (hg : g ∈ unipotent) (hne : g ≠ 1) :
    2 ≤ operatorFixedCodim (Natural.action F g) := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  have he := operatorFixedCodim_eq_of_equiv (Natural.action F (unipotentProduct t))
    (Restricted.NaturalCoordinates.action F (unipotentProduct t)) (Restricted.NaturalCoordinates.equiv F)
    (fun v => LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' (unipotentProduct t)) v)
  rw [he]
  by_contra! h
  exact hne (product_eq_one_of_small_rank t (by omega))


open scoped Pointwise

private theorem exists_in_unipotent [Finite F] (g : Model F) (hne : g ≠ 1) (hg : g * g = 1) :
    ∃ a : Model F, a * g * a⁻¹ ∈ unipotent := by
  have ho : orderOf g = 2 := orderOf_eq_prime (by simpa only [pow_two] using hg) hne
  have hp : IsPGroup 2 (Subgroup.zpowers g) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ho, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (Model F) S (LieParabolicSetup.sylow (F := F))
  refine ⟨a, ?_⟩
  have hm : (MulAut.conj a) g ∈ (MulAut.conj a) • (S : Subgroup (Model F)) :=
    Subgroup.mem_map.mpr ⟨g, hS (Subgroup.mem_zpowers g), rfl⟩
  change a * g * a⁻¹ ∈ (a • S : Sylow 2 (Model F)) at hm
  rw [ha] at hm
  exact hm

private theorem natural_rank_conj (a g : Model F) :
    operatorFixedCodim (Natural.action F g) =
      operatorFixedCodim (Natural.action F (a * g * a⁻¹)) := by
  let ρ := Natural.action F
  apply operatorFixedCodim_eq_of_equiv _ _
    (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a))
  intro v
  change ρ a (ρ g v) = ρ (a * g * a⁻¹) (ρ a v)
  simp only [← Module.End.mul_apply, ← map_mul]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Square-zero displacement bounds the natural rank of any involution by three. -/
theorem operatorFixedCodim_le_three_of_involution (g : Model F) (hg : g * g = 1) :
    operatorFixedCodim (Natural.action F g) ≤ 3 := by
  let T := Natural.action F g
  have hh (v : Natural.Space F) : T (T v) = v := by
    change Natural.action F g (Natural.action F g v) = v
    rw [← Module.End.mul_apply, ← map_mul, hg, map_one, Module.End.one_apply]
  have hadd (v : Natural.Space F) : v + v = 0 := by
    have h := congrArg (fun c : F => c • v) (CharTwo.add_self_eq_zero (1 : F))
    simpa only [add_smul, one_smul, zero_smul] using h
  have hincl : (T - 1).range ≤ (T - 1).ker := by
    rintro _ ⟨v, rfl⟩
    change T (T v - v) - (T v - v) = 0
    rw [map_sub, hh]
    calc
      v - T v - (T v - v) = (v + v) - (T v + T v) := by abel
      _ = 0 := by rw [hadd, hadd, sub_self]
  have hm := Submodule.finrank_mono hincl
  have hr := (T - 1).finrank_range_add_finrank_ker
  rw [Natural.finrank_space] at hr
  change finrank F (T - 1).range ≤ 3
  omega

/-- The universal no-transvection statement on the literal natural G₂ module. -/
theorem two_le_operatorFixedCodim_of_involution [Finite F]
    (g : Model F) (hne : g ≠ 1) (hg : g * g = 1) :
    2 ≤ operatorFixedCodim (Natural.action F g) := by
  obtain ⟨a, ha⟩ := exists_in_unipotent g hne hg
  rw [natural_rank_conj a g]
  apply two_le_operatorFixedCodim_of_mem_unipotent _ ha
  intro h
  apply hne
  exact (MulAut.conj a).injective (h.trans (map_one (MulAut.conj a)).symm)

/-- The two possible natural displacement ranks of a nonidentity involution. -/
theorem operatorFixedCodim_bounds [Finite F]
    (g : Model F) (hne : g ≠ 1) (hg : g * g = 1) :
    2 ≤ operatorFixedCodim (Natural.action F g) ∧
      operatorFixedCodim (Natural.action F g) ≤ 3 :=
  ⟨two_le_operatorFixedCodim_of_involution g hne hg,
    operatorFixedCodim_le_three_of_involution g hg⟩

end Atlas.G2.Natural.InvolutionRank
