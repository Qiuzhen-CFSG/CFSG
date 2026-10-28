module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SuzukiPanelCompletion
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanPinning
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.LinearPlacement

/-!
# Completing a linear root marking to the whole faithful endpoint

The full abelian Cartan centralizes the internal rank-one torus. Since
squaring is bijective in the finite field of characteristic two, its
conjugation action on the canonical root is scalar. The internal torus
realizes the same scalar, so their difference belongs to the literal
panel kernel. Thus the whole endpoint is the product of its root-generated
group and panel kernel. Centerlessness of PSL₂ identifies the full quotient.

The equivalence extends the supplied root marking exactly. The canonical
root maps to a full Sylow, and the entire quotient Borel maps to its
normalizer. All fields, including F₂, are retained; there is no endpoint
perfectness or Weyl-order hypothesis. The scalar argument specializes the
existing GTwoSource.CommonField proof to one endpoint, so the opposite
endpoint need not be linear. The original-factor application is in
CFSG's FongSeitzBinary.LinearPanelCompletion.

Source: Fong--Seitz I (3B), (5C), pp.13,25--26; II §7, p.192;
DGS, Groups and Graphs (1985), Theorem D, p.224.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelCompletion
open RootCoordinates HexagonStructure GTwoSource ReeSource
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : localGroup Q split i ≃* PSL(2,F)) (n : HexagonStructure.RootReflection Q split i)

/-- Every element of the full Cartan acts by a scalar in each actual
rank-one labeling. This follows from commuting with all own-root squares. -/
theorem linear_cartan_scalar {t : X ⧸ Q.D}
    (ht : t ∈ Q.tits.B ⊓ Q.tits.N) :
    ∃ b : Fˣ, ∀ c : F,
      MulAut.conj t (alignedSimpleParameter Q split i hV μ n (.ofAdd c)) =
        alignedSimpleParameter Q split i hV μ n (.ofAdd ((b : F)*c)) := by
  let U := alignedSimpleParameter Q split i hV μ n
  let T := alignedTorusHom Q split i hV μ n
  have hinj : Function.Injective (fun c : F => U (.ofAdd c)) :=
    (alignedSimpleParameter_injective Q split i hV μ n).comp
      Multiplicative.ofAdd.injective
  have hmem : MulAut.conj t (U (.ofAdd (1 : F))) ∈ simpleRoot Q split i :=
    (mem_normalizer_iff.mp (torus_normalizes_simpleRoot Q split i ht) _).mp
      (alignedSimpleParameter_range Q split i hV μ n ▸ ⟨.ofAdd 1,rfl⟩)
  rw [←alignedSimpleParameter_range Q split i hV μ n] at hmem
  obtain ⟨b,hb⟩ := hmem
  have hval : MulAut.conj t (U (.ofAdd (1 : F))) = U (.ofAdd b.toAdd) := hb.symm
  have hb0 : b.toAdd ≠ 0 := by
    intro hz
    have he : MulAut.conj t (U (.ofAdd (1 : F))) = MulAut.conj t (U (.ofAdd (0 : F))) := by
      simpa only [hz,ofAdd_zero,map_one] using hval
    exact one_ne_zero (hinj ((MulAut.conj t).injective he))
  refine ⟨Units.mk0 b.toAdd hb0, ?_⟩
  intro c
  by_cases hc : c = 0
  · simp only [hc,mul_zero,ofAdd_zero,map_one]
  obtain ⟨a,ha⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R := F))) c
  change a^2=c at ha
  have ha0 : a ≠ 0 := by intro hz; apply hc; rw [←ha,hz]; simp
  let a' := Units.mk0 a ha0
  have hcomm : Commute t (T a') := by
    let := split.abelian
    exact congrArg Subtype.val (mul_comm
      (⟨t,ht⟩ : ↥(Q.tits.B ⊓ Q.tits.N))
      (⟨_,alignedTorus_mem_cartan Q split i hV μ n a'⟩ :
        ↥(Q.tits.B ⊓ Q.tits.N)))
  have hfix : MulAut.conj t (T a') = T a' := by
    change t*T a'*t⁻¹=T a'
    rw [hcomm.eq,mul_assoc,mul_inv_cancel,mul_one]
  have hown := alignedTorus_root Q split i hV μ n a' 1
  change T a' * U (.ofAdd (1 : F)) * (T a')⁻¹ = U (.ofAdd ((a : F)^2*1)) at hown
  rw [mul_one,ha] at hown
  have he := congrArg (MulAut.conj t) hown
  rw [map_mul,map_mul,map_inv,hfix,hval] at he
  have hscale := alignedTorus_root Q split i hV μ n a' b.toAdd
  change T a' * U (.ofAdd b.toAdd) * (T a')⁻¹ = U (.ofAdd (a^2*b.toAdd)) at hscale
  rw [hscale,ha] at he
  simpa only [Units.val_mk0,mul_comm c b.toAdd] using he.symm

include hV μ n in
/-- Every full Cartan action is realized inside the root-generated group. -/
theorem linear_cartan_le_root_sup_kernel :
    Q.tits.B ⊓ Q.tits.N ≤ rankOne Q split i ⊔ localKernel Q i := by
  intro h hh
  obtain ⟨b,hb⟩ := linear_cartan_scalar Q split i hV μ n hh
  have hinj : Function.Injective (fun a : Fˣ => a^2) := by
    intro a c he
    exact Units.ext (CharTwo.sq_injective (congrArg Units.val he))
  obtain ⟨a,ha⟩ := (Finite.surjective_of_injective hinj) b
  have haF : (a : F)^2 = (b : F) := congrArg Units.val ha
  let c := alignedTorusHom Q split i hV μ n a
  have hcH : c ∈ Q.tits.B ⊓ Q.tits.N := alignedTorus_mem_cartan Q split i hV μ n a
  have hcR : c ∈ rankOne Q split i :=
    ((alignedTorusHom_range Q split i hV μ n).le ⟨a,rfl⟩).2
  have hkH : c⁻¹*h ∈ Q.tits.B ⊓ Q.tits.N :=
    (Q.tits.B ⊓ Q.tits.N).mul_mem ((Q.tits.B ⊓ Q.tits.N).inv_mem hcH) hh
  have hkC : c⁻¹*h ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) := by
    intro x hx
    rw [←alignedSimpleParameter_range Q split i hV μ n] at hx
    obtain ⟨z,rfl⟩ := hx
    have hact := hb z.toAdd
    have hown := alignedTorus_root Q split i hV μ n a z.toAdd
    rw [haF] at hown
    have he : h * alignedSimpleParameter Q split i hV μ n z * h⁻¹ =
        c * alignedSimpleParameter Q split i hV μ n z * c⁻¹ := hact.trans hown.symm
    have he' : (c⁻¹*h)*alignedSimpleParameter Q split i hV μ n z*(c⁻¹*h)⁻¹ =
        alignedSimpleParameter Q split i hV μ n z := by
      calc
        _ = c⁻¹*(h*alignedSimpleParameter Q split i hV μ n z*h⁻¹)*c := by group
        _ = _ := by rw [he]; group
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  have hk : c⁻¹*h ∈ localKernel Q i :=
    ((cartan_centralizer_simpleRoot Q split i).le ⟨hkH,hkC⟩).2
  simpa only [mul_inv_cancel_left] using
    (rankOne Q split i ⊔ localKernel Q i).mul_mem (mem_sup_left hcR) (mem_sup_right hk)

include hV in
/-- The full faithful linear panel, with its whole Borel and canonical Sylow.
The specified root marking is retained exactly, without an inner adjustment. -/
theorem exists_linear_panel_marking
    (η : rankOne Q split i ≃* PSL(2,F)) :
    ∃ (σ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL(2,F))
      (T : Sylow 2 PSL(2,F)),
      (∀ r, σ (rootPanelMap Q split i r) = η r) ∧
      (rootProjection Q split i).range.map σ.toMonoidHom = (T : Subgroup PSL(2,F)) ∧
      (quotientBorel Q i).map σ.toMonoidHom = normalizer (T : Set PSL(2,F)) := by
  have hz : center (rankOne Q split i) = ⊥ := by
    apply eq_bot_iff.mpr
    intro r hr
    have hη := MulEquivClass.apply_mem_center η hr
    change η r ∈ center PSL(2,F) at hη
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hη
    exact η.injective (hη.trans η.map_one.symm)
  let ν := QuadrangleStructure.localGroupEquivOfCenterless Q split i hV η
    BenderSuzuki.ZD.Linear.psl2_center_eq_bot
  have hH := linear_cartan_le_root_sup_kernel Q split i hV ν
    (UnitarySource.actorReflection Q split i)
  let e := MulEquiv.ofBijective (rootPanelMap Q split i)
    ⟨rootPanelMap_injective Q split i hz, rootPanelMap_surjective Q split i hV hH⟩
  obtain ⟨S,hS⟩ := QuadrangleStructure.simpleRoot_sylow_of_linear Q split i hV
    (η.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
  let T := S.mapSurjective (f := η.toMonoidHom) η.surjective
  have hT : ((simpleRoot Q split i).subgroupOf (rankOne Q split i)).map η.toMonoidHom =
      (T : Subgroup PSL(2,F)) := by
    rw [←hS]
    rfl
  let σ := e.symm.trans η
  have he (r : rankOne Q split i) : σ (rootPanelMap Q split i r) = η r :=
    congrArg η (e.symm_apply_apply r)
  have hf : σ.toMonoidHom.comp (rootPanelMap Q split i) = η.toMonoidHom := by
    ext r : 1
    exact he r
  refine ⟨σ,T,he,?_,?_⟩
  · have hp : rootProjection Q split i = (rootPanelMap Q split i).comp
        (inclusion (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left)) := by
      ext r
      rw [MonoidHom.comp_apply,rootPanelMap_apply,rootProjection_apply]
      rfl
    rw [hp,MonoidHom.range_comp,map_map,hf,inclusion_range]
    exact hT
  · have hb : Q.tits.B.subgroupOf (rankOne Q split i) =
        normalizer (((simpleRoot Q split i).subgroupOf (rankOne Q split i)) : Set _) := by
      ext r
      exact rankOne_borel_iff_root_normalizer Q split i hV r
    have hmap : (Q.tits.B.subgroupOf (rankOne Q split i)).map e.toMonoidHom = quotientBorel Q i := by
      change ((Q.tits.B.subgroupOf (rankOne Q split i)).map (rootPanelMap Q split i)) = _
      rw [←rootPanelMap_borel,map_comap_eq_self_of_surjective
        (rootPanelMap_surjective Q split i hV hH)]
    rw [←hmap,map_map]
    change (Q.tits.B.subgroupOf (rankOne Q split i)).map
      (σ.toMonoidHom.comp (rootPanelMap Q split i)) = _
    rw [hf,hb,map_normalizer_eq_of_bijective _ η.bijective,hT]
    rfl

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelCompletion
