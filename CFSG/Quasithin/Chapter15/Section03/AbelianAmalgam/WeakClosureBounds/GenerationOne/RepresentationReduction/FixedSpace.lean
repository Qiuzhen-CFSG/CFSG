module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.Setup
public import Theory.Representation.BinaryOffender.IrreducibleSection
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Fixed-space reduction in the generation-one argument

The B.2.14 decomposition separates the commutator space from the global fixed
space. A calculation on the former therefore suffices to fix the literal seed.
On a central extension, vanishing of Borel-fixed vectors in the actual quotient
puts every fixed lift in its centralized kernel; no splitting is needed.

These are conditional assembly lemmas for Aschbacher--Smith, 15.3.65, printed
p.1152. The representation classification and the model fixed-space calculations
must still supply their premises. In particular none asserts the source lemma.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
open Subgroup ChapterE Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative

section Linear
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- Fixation by two subgroups gives fixation by their join. -/
theorem le_fixedSpace_sup {S : Submodule (ZMod 2) V} {A B : Subgroup D}
    (hA : S ≤ fixedSpace ρ A) (hB : S ≤ fixedSpace ρ B) :
    S ≤ fixedSpace ρ (A ⊔ B) := by
  have h : A ⊔ B ≤ subspaceKernel ρ S ⊤ := sup_le
    (fun a ha => ⟨mem_top _, fun v hv => hA hv ⟨a, ha⟩⟩)
    (fun b hb => ⟨mem_top _, fun v hv => hB hv ⟨b, hb⟩⟩)
  intro v hv g
  exact (h g.property).2 v hv

/-- A central summand can be removed from the Borel-fixed-space calculation.
The hypothesis only concerns the commutator summand W. -/
theorem fixedSpace_le_of_decomposition {K T B : Subgroup D}
    {W S : Submodule (ZMod 2) V}
    (hgen : K ⊔ T = ⊤) (hdecomp : W ⊔ fixedSpace ρ ⊤ = ⊤)
    (hW : W ⊓ fixedSpace ρ B ≤ fixedSpace ρ K)
    (hB : S ≤ fixedSpace ρ B) (hT : S ≤ fixedSpace ρ T) :
    S ≤ fixedSpace ρ ⊤ := by
  have hK : S ≤ fixedSpace ρ K := by
    intro v hv
    have hmem : v ∈ W ⊔ fixedSpace ρ ⊤ := by rw [hdecomp]; trivial
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hmem
    have hcw : c ∈ fixedSpace ρ B := fun b => hc ⟨b, mem_top _⟩
    have hwB : w ∈ fixedSpace ρ B := by
      have h := (fixedSpace ρ B).sub_mem (hB hv) hcw
      simpa only [add_sub_cancel_right] using h
    exact (fixedSpace ρ K).add_mem (hW ⟨hw, hwB⟩)
      (fun k => hc ⟨k, mem_top _⟩)
  simpa only [hgen] using le_fixedSpace_sup ρ hK hT

/-- Transport vanishing fixed vectors through a genuine equivariant linear
identification, including a surjective model map on the Borel. -/
theorem fixedSpace_eq_bot_of_equivariant
    {E X : Type*} [Group E] [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) E X) (φ : D →* E)
    (e : V ≃ₗ[ZMod 2] X) (he : ∀ g v, e (ρ g v) = σ (φ g) (e v))
    (B : Subgroup D) (B' : Subgroup E) (hB : B.map φ = B')
    (hzero : fixedSpace σ B' = ⊥) : fixedSpace ρ B = ⊥ := by
  apply bot_unique
  intro v hv
  have hx : e v ∈ fixedSpace σ B' := by
    rintro ⟨b, hb⟩
    rw [← hB] at hb
    obtain ⟨g, hg, rfl⟩ := hb
    change σ (φ g) (e v) = e v
    exact (he g v).symm.trans (congrArg e (hv ⟨g, hg⟩))
  rw [hzero] at hx
  exact e.injective (hx.trans e.map_zero.symm)

/-- An extension of a fixed-point-free Borel module over a centralized
submodule has only globally fixed Borel-fixed vectors. The quotient is literal. -/
theorem fixedSpace_le_of_central_extension
    (C : Subrepresentation ρ) (hC : C.toSubmodule ≤ fixedSpace ρ ⊤)
    (B : Subgroup D) (hquot : fixedSpace C.quotientRepresentation B = ⊥) :
    fixedSpace ρ B ≤ fixedSpace ρ ⊤ := by
  intro v hv
  have hq : C.toSubmodule.mkQ v ∈ fixedSpace C.quotientRepresentation B := by
    intro b
    change C.toSubmodule.mkQ (ρ b v) = C.toSubmodule.mkQ v
    exact congrArg C.toSubmodule.mkQ (hv b)
  rw [hquot] at hq
  exact hC ((Submodule.Quotient.mk_eq_zero _).mp hq)

/-- The preceding extension argument on an invariant subspace and its actual
central quotient I/C_I(K). This includes non-split Irr⁺ sections. -/
theorem inf_fixedSpace_le_of_centralQuotient
    (K B : Subgroup D) (I : Submodule (ZMod 2) V)
    (hI : K ≤ subspaceStabilizer ρ I)
    (hquot : fixedSpace (centralQuotientRepresentation ρ K I hI)
      (B.subgroupOf K) = ⊥) :
    I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K := by
  rintro v ⟨hvI, hvB⟩
  let w : I := ⟨v, hvI⟩
  let q := ((fixedSpace ρ K).comap I.subtype).mkQ
  have hq : q w ∈ fixedSpace (centralQuotientRepresentation ρ K I hI)
      (B.subgroupOf K) := by
    intro b
    change q ⟨ρ b.val w, (hI b.val.property w).2 w.property⟩ = q w
    congr 1
    exact Subtype.ext (hvB ⟨b.val, b.property⟩)
  rw [hquot] at hq
  exact (Submodule.Quotient.mk_eq_zero ((fixedSpace ρ K).comap I.subtype)).mp hq

end Linear

section Local
variable {G : Type*} [Group G]

/-- The quotient image version of Setup's commutator criterion for a subgroup
of H. Relative containment is explicit; no ambient normality is used. -/
theorem seedSpace_le_actorImage_iff
    {H U Z ZS L : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (hZU : ZS ≤ U) (hLH : L ≤ H) :
    seedSpace a ZS ≤ fixedSpace a.representation (actorImage H L) ↔ ⁅ZS, L⁆ ≤ Z := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_le]
  constructor
  · intro h l hl z hz
    let zU : U := ⟨z, hZU hz⟩
    let lH : H := ⟨l, hLH hl⟩
    have hv := h (Submodule.subset_span
      (show Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) zU) ∈
          {v | ∃ z : U, (z : G) ∈ ZS ∧
            Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) z) = v} from
        ⟨zU, hz, rfl⟩))
      ⟨QuotientGroup.mk' (pCore 2 H) lH, ⟨lH, hl, rfl⟩⟩
    change a.representation (QuotientGroup.mk' (pCore 2 H) lH)
      (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) zU)) = _ at hv
    rw [a.conjugation] at hv
    have hm := QuotientGroup.eq_iff_div_mem.mp (congrArg Additive.toMul hv)
    change l * z * l⁻¹ / z ∈ Z at hm
    simpa only [div_eq_mul_inv, commutatorElement_def] using hm
  · intro h
    apply Submodule.span_le.mpr
    rintro v ⟨z, hz, rfl⟩ ⟨hq, k, hk, rfl⟩
    change a.representation (QuotientGroup.mk' (pCore 2 H) k)
      (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) z)) = _
    rw [a.conjugation]
    apply congrArg Additive.ofMul
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (k : G) * z * (k : G)⁻¹ / z ∈ Z
    simpa only [div_eq_mul_inv, commutatorElement_def] using h k hk z hz

/-- Borel fixation from the two-residual input and the existing T-fixation.
The supplied Sylow subgroup is internal to B and is embedded into T. -/
theorem seedSpace_le_borel_of_residual_and_sylow [Finite G]
    {H U Z ZS B T : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (hZU : ZS ≤ U) (hBH : B ≤ H) (hTH : T ≤ H)
    (S : Sylow 2 B) (hST : (S : Subgroup B).map B.subtype ≤ T)
    (hres : ⁅ZS, residual B⁆ ≤ Z)
    (hT : seedSpace a ZS ≤ fixedSpace a.representation (actorImage H T)) :
    seedSpace a ZS ≤ fixedSpace a.representation (actorImage H B) := by
  have hs := congrArg (fun K : Subgroup B => K.map B.subtype)
    (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hs
  change residual B ⊔ (S : Subgroup B).map B.subtype = B at hs
  have hRH : residual B ≤ H := (residual_le B).trans hBH
  have hSH : (S : Subgroup B).map B.subtype ≤ H := hST.trans hTH
  have hi : actorImage H B = actorImage H (residual B) ⊔
      actorImage H ((S : Subgroup B).map B.subtype) := by
    conv_lhs => rw [← hs]
    simp only [actorImage, subgroupOf_sup hRH hSH, Subgroup.map_sup]
  rw [hi]
  apply le_fixedSpace_sup
  · exact (seedSpace_le_actorImage_iff a hZU hRH).mpr hres
  · apply (seedSpace_le_actorImage_iff a hZU hSH).mpr
    exact (commutator_mono le_rfl hST).trans
      ((seedSpace_le_actorImage_iff a hZU hTH).mp hT)

/-- The last linear step on U/Z, conditional on B.2.14 and the calculation
on its commutator subspace. The latter premise remains a model obligation. -/
theorem seedSpace_le_fixedSpace_of_borel_calculation
    {H U Z ZS M T : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z)
    (hgen : actorImage H (residual H) ⊔ actorImage H T = ⊤)
    (hdecomp : subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ⊔
      fixedSpace a.representation ⊤ = ⊤)
    (hcalc : subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ⊓
      fixedSpace a.representation (borelImage H M) ≤
        fixedSpace a.representation (actorImage H (residual H)))
    (hB : seedSpace a ZS ≤ fixedSpace a.representation (borelImage H M))
    (hT : seedSpace a ZS ≤ fixedSpace a.representation (actorImage H T)) :
    seedSpace a ZS ≤ fixedSpace a.representation ⊤ :=
  fixedSpace_le_of_decomposition a.representation hgen hdecomp hcalc hB hT

end Local
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
