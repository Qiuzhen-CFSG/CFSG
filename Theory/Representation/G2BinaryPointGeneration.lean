module
public import Theory.Representation.G2BinaryPointOffenders
public import Theory.Representation.G2NaturalFaithfulness
/-!
# Two opposite root eights in the binary natural G₂ group

The longest Weyl element exchanges the two halves of the natural six-space.
Multiplying it by B(1)C(1) gives an element of order seven with the same
conjugate of the A–B–C eight. Short checked root words recover the six
positive roots and the two Weyl generators from these two eights.
The order-seven element has no fixed vector, giving residual codimension six.
These calculations supply exactly the generation and dimension inputs of
Baumann's argument in C.1.37 and 13.3.10(2), printed pp.143,887–888 of
Aschbacher–Smith. Root coordinates retain the attribution in LICENSES/ATLAS.txt.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Atlas.G2.Natural.BinaryPointGeneration
open Restricted.NaturalCoordinates NaturalOffenders
local notation "𝔽" => ZMod 2
local notation "H" => Model 𝔽
local notation "ρ" => Restricted.NaturalCoordinates.action 𝔽

private theorem coordinate_injective : Function.Injective ρ := by
  intro g h he
  apply Natural.action_injective 𝔽
  apply LinearMap.ext
  intro v
  apply (equiv 𝔽).injective
  have hh := LinearMap.congr_fun he (equiv 𝔽 v)
  exact ((repEquiv 𝔽).isIntertwining g v).trans
    (hh.trans ((repEquiv 𝔽).isIntertwining h v).symm)

private def w : H := (weylR * weylS)^3
private theorem w_square : w*w = 1 := by
  apply coordinate_injective
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [w,pow_succ,map_mul,Module.End.mul_apply]

private theorem w_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right w_square
private def g : H := w * rootB 1 * rootC 1
private theorem g_inv : g⁻¹ = rootC 1 * rootB 1 * w := by
  have hb : (rootB (1:𝔽))⁻¹ = rootB 1 := inv_eq_of_mul_eq_one_right (by
    rw [rootB_add,show (1:𝔽)+1=0 by decide,rootB_zero])
  have hc : (rootC (1:𝔽))⁻¹ = rootC 1 := inv_eq_of_mul_eq_one_right (by
    rw [rootC_add,show (1:𝔽)+1=0 by decide,rootC_zero])
  simp only [g,mul_inv_rev,hb,hc,w_inv,mul_assoc]

private theorem action_w (v : Fin 6 → 𝔽) :
    ρ w v = ![v 5,v 4,v 3,v 2,v 1,v 0] := by
  ext i
  fin_cases i <;> simp [w,pow_succ,map_mul,Module.End.mul_apply]

private theorem action_g (v : Fin 6 → 𝔽) :
    ρ g v = ![v 5,v 4,v 3,v 2+v 4+v 5,v 1+v 3,v 0+v 5+v 3] := by
  ext i
  fin_cases i <;> simp [g,map_mul,Module.End.mul_apply,action_w]

private theorem g_seven : g^7 = 1 := by
  apply coordinate_injective
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [pow_succ,map_mul,Module.End.mul_apply,action_g] <;>
    (ring_nf; reduce_mod_char!)

private def na : H := w * rootA 1 * w
private def nb : H := w * rootB 1 * w
private def nc : H := w * rootC 1 * w

private theorem negative_mem (r : H) (hr : r ∈ BinaryCore.elementary) :
    w*r*w ∈ BinaryCore.elementary.map (MulAut.conj g).toMonoidHom := by
  have hh : rootB (1:𝔽) * rootC 1 ∈ BinaryCore.elementary := by
    rw [BinaryModelOffenders.elementary_eq]
    exact (EvenTwoRank.elementary 𝔽).mul_mem (rootB_mem_elementary 1) (rootC_mem_elementary 1)
  have hc : Commute (rootB (1:𝔽)*rootC 1) r := by
    exact congrArg (fun x : BinaryCore.elementary => (x : H))
      ((inferInstance : IsMulCommutative BinaryCore.elementary).is_comm.comm ⟨_,hh⟩ ⟨_,hr⟩)
  refine ⟨r,hr,?_⟩
  change g*r*g⁻¹ = _
  rw [show g = w*(rootB 1*rootC 1) by simp [g,mul_assoc],mul_inv_rev,w_inv]
  calc
    _ = w * ((rootB 1*rootC 1)*r*(rootB 1*rootC 1)⁻¹) * w := by group
    _ = _ := by rw [hc.eq,mul_inv_cancel_right]

private theorem wordD : na * rootA 1 * nc * rootA 1 * na = rootD (1:𝔽) := by
  apply coordinate_injective
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [na,nc,map_mul,Module.End.mul_apply,action_w] <;> (ring_nf; reduce_mod_char!)
private theorem wordE : rootA 1 * nb * rootA 1 * nb = rootE (1:𝔽) := by
  apply coordinate_injective
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [nb,map_mul,Module.End.mul_apply,action_w] <;> (ring_nf; reduce_mod_char!)
private theorem wordF : nb * rootB 1 * nc * rootB 1 * nb = rootF (1:𝔽) := by
  apply coordinate_injective
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [nb,nc,map_mul,Module.End.mul_apply,action_w] <;> (ring_nf; reduce_mod_char!)
private theorem wordR : rootA 1 * rootB 1 * na * nb * rootA 1 * rootB 1 * na * nb = (weylR : H) := by
  apply coordinate_injective
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [na,nb,map_mul,Module.End.mul_apply,action_w] <;> (ring_nf; reduce_mod_char!)
private theorem wordS : rootB 1 * rootC 1 * nc * rootA 1 * rootC 1 * na * rootB 1 * nb * rootB 1 = (weylS : H) := by
  apply coordinate_injective
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [na,nb,nc,map_mul,Module.End.mul_apply,action_w] <;> (ring_nf; reduce_mod_char!)


private theorem fixed_g_eq_zero (v : Fin 6 → 𝔽) (hv : ρ g v = v) : v = 0 := by
  have hh (i : Fin 6) := congrFun hv i
  simp only [action_g] at hh
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  have h4 := hh 4
  have h5 := hh 5
  change v 5 = v 0 at h0
  change v 4 = v 1 at h1
  change v 3 = v 2 at h2
  change v 2 + v 4 + v 5 = v 3 at h3
  change v 1 + v 3 = v 4 at h4
  change v 0 + v 5 + v 3 = v 5 at h5
  have hd : v 3 = 0 := by linear_combination h4 + h1
  have ha : v 0 = 0 := by linear_combination h5 - hd
  have hf : v 5 = 0 := by linear_combination h0 + ha
  have he : v 4 = 0 := by linear_combination h3 + h2 - hf
  have hb : v 1 = 0 := by linear_combination he - h1
  have hc : v 2 = 0 := by linear_combination hd - h2
  ext i
  fin_cases i <;> simp [ha,hb,hc,hd,he,hf]

/-- The same odd-order actor detects that the residual fixes no natural vector. -/
theorem fixedSpace_residual : Representation.BinaryOffender.fixedSpace ρ (pResidual 2 H) = ⊥ := by
  have hg : g ∈ pResidual 2 H := mem_pResidual_of_orderOf_coprime
    ((show Nat.Coprime 2 7 from by decide).of_dvd_right (orderOf_dvd_of_pow_eq_one g_seven))
  apply bot_unique
  intro v hv
  exact fixed_g_eq_zero v (hv ⟨g,hg⟩)

/-- The residual has codimension six on the literal natural six-space. -/
theorem fixedCodim_residual : Representation.BinaryOffender.fixedCodim ρ (pResidual 2 H) = 6 := by
  have hh := Representation.BinaryOffender.fixedCodim_add_finrank ρ (pResidual 2 H)
  rw [fixedSpace_residual,finrank_bot,add_zero] at hh
  simpa using hh

/-- The root eight and an odd-order residual conjugate generate the full group. -/
theorem exists_residual_conjugate_generating :
    ∃ c ∈ pResidual 2 H, BinaryCore.elementary ⊔
      BinaryCore.elementary.map (MulAut.conj c).toMonoidHom = ⊤ := by
  have hg : g ∈ pResidual 2 H := mem_pResidual_of_orderOf_coprime
    ((show Nat.Coprime 2 7 from by decide).of_dvd_right (orderOf_dvd_of_pow_eq_one g_seven))
  refine ⟨g,hg,?_⟩
  let K := BinaryCore.elementary ⊔ BinaryCore.elementary.map (MulAut.conj g).toMonoidHom
  have ha : rootA (1:𝔽) ∈ BinaryCore.elementary := by
    rw [BinaryModelOffenders.elementary_eq]; exact rootA_mem_elementary 1
  have hb : rootB (1:𝔽) ∈ BinaryCore.elementary := by
    rw [BinaryModelOffenders.elementary_eq]; exact rootB_mem_elementary 1
  have hc : rootC (1:𝔽) ∈ BinaryCore.elementary := by
    rw [BinaryModelOffenders.elementary_eq]; exact rootC_mem_elementary 1
  have hA : rootA (1:𝔽) ∈ K := mem_sup_left ha
  have hB : rootB (1:𝔽) ∈ K := mem_sup_left hb
  have hC : rootC (1:𝔽) ∈ K := mem_sup_left hc
  have hnA : na ∈ K := mem_sup_right (negative_mem _ ha)
  have hnB : nb ∈ K := mem_sup_right (negative_mem _ hb)
  have hnC : nc ∈ K := mem_sup_right (negative_mem _ hc)
  have hD : rootD (1:𝔽) ∈ K := wordD ▸ K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hnA hA) hnC) hA) hnA
  have hE : rootE (1:𝔽) ∈ K := wordE ▸ K.mul_mem (K.mul_mem (K.mul_mem hA hnB) hA) hnB
  have hF : rootF (1:𝔽) ∈ K := wordF ▸ K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hnB hB) hnC) hB) hnB
  have hR : (weylR : H) ∈ K := wordR ▸ K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem
    (K.mul_mem (K.mul_mem (K.mul_mem hA hB) hnA) hnB) hA) hB) hnA) hnB
  have hS : (weylS : H) ∈ K := wordS ▸ K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem
    (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hB hC) hnC) hA) hC) hnA) hB) hnB) hB
  have hroot (f : 𝔽 → H) (hzero : f 0 = 1) (hone : f 1 ∈ K) (a : 𝔽) : f a ∈ K := by
    rcases (show ∀ a : 𝔽, a=0 ∨ a=1 by decide) a with rfl|rfl
    · exact hzero ▸ K.one_mem
    · exact hone
  have hU : unipotent (K := 𝔽) ≤ K := by
    rw [unipotent_eq_range]
    rintro _ ⟨t,rfl⟩
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem
      (hroot rootA rootA_zero hA (t 0)) (hroot rootB rootB_zero hB (t 1)))
      (hroot rootC rootC_zero hC (t 2))) (hroot rootD rootD_zero hD (t 3)))
      (hroot rootE rootE_zero hE (t 4))) (hroot rootF rootF_zero hF (t 5))
  apply top_unique
  rw [← Atlas.G2.generated_eq_top (F := 𝔽)]
  apply sup_le
  · apply (closure_le K).mpr
    rintro x (hx|hx)
    · exact hU hx
    · rcases hx with rfl|hx
      · exact hR
      · exact (Set.mem_singleton_iff.mp hx) ▸ hS
  · rintro _ ⟨p,rfl⟩
    have hp : p = 1 := (show ∀ p : 𝔽ˣ × 𝔽ˣ, p=1 by decide) p
    rw [hp,map_one]
    exact K.one_mem

end Atlas.G2.Natural.BinaryPointGeneration
