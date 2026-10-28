module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.DualNatural
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.Basic
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The actual dual natural section in the H-chief accounting

The earlier source duality has denominator C_U(O₂(H)), which can be smaller
than U₀. The checked central-cover comparison factors the original natural
projection through that section. The dual of this surjection has image exactly
Q_K/C_H(U): K centralizes U₀, giving the annihilator containment, and the
marked SL₂(4) generates its dual natural module by commutators, giving equality.
Inverting that embedding constructs coordinates on the literal Q_K section,
retaining the original naturalMap and every functional's commutator kernel.
Both annihilators are identified in the original ambient group.

The earlier SourceDuality and [U,O₂(H)]=V₁ remain genuine inputs from
14.5.21(1–2), owned by qt-14-05-terminal-duality and discharged in qt-14-07.
No simplicity of U/V₁ or equality U₀=V₁ is used. Chief accounting is separate.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.5.21, printed pp.1019–1020, and 14.7.71, printed p.1075 (PDF p.1092).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

theorem QK_centralizes_fixed : QK F ≤ centralizer (d.U₀ : Set G) := by
  apply sup_le
  · exact (commutator_mono le_rfl d.K_centralizes_U₀).trans
      (le_normalizer_iff_commutator_le_right.mp
        ((pCoreIn_le 2 F.H).trans
          (d.H_normalizes_U₀.trans (normalizer_le_normalizer_centralizer d.U₀))))
  · exact inf_le_right.trans (centralizer_le d.U₀_le_U)

omit [Finite G] in
private theorem imageSpace_mem_of_kernel_le
    (s : CriticalIntersections.SourceDuality F X Y)
    (B : Subgroup G) (hB : F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) ≤ B)
    (q : F.H.pCoreIn 2) :
    (s.qSection.coordinates q).toAdd ∈ s.qSection.imageSpace B ↔ (q : G) ∈ B := by
  constructor
  · intro hq
    obtain ⟨r, hr, he⟩ := (s.qSection.mem_imageSpace_iff B _).mp hq
    have hk : (q / r : F.H.pCoreIn 2).val ∈ F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) := by
      apply (s.qSection.coordinates_eq_one_iff _).mp
      rw [map_div, Multiplicative.toAdd.injective he, div_self']
    simpa using B.mul_mem (hB hk) hr
  · intro hq
    exact (s.qSection.mem_imageSpace_iff B _).mpr ⟨q, hq, rfl⟩

/-- On a marked alternating lift the dual keeps the original SL₂(4) actor. -/
theorem natural_dual_on_lift (k : F.H) (g : SL2FourNatural.SL)
    (hk : d.qH k = alternatingActor d.naturalQuotient g)
    (a : Module.Dual (ZMod 2) SL2FourNatural.V) :
    (naturalAction d).dual k a = SL2FourNatural.naturalRepresentation.dual g a := by
  apply LinearMap.ext
  intro v
  change a (d.naturalQuotient.action (d.qH k⁻¹) v) =
    a (SL2FourNatural.action g⁻¹ v)
  rw [map_inv, hk, ← map_inv]
  exact congrArg a (d.naturalQuotient.restriction g⁻¹ v)

/-- The commutator image is the range of the dual of the original projection.
The projection may have a nonzero fixed kernel. -/
theorem qK_image_eq_dual_range
    (s : CriticalIntersections.SourceDuality F X Y)
    (p : s.uAction.IntertwiningMap (naturalAction d))
    (hp : Function.Surjective p)
    (hcoord : ∀ v : F.U, p (s.uSection.coordinates v).toAdd = (naturalMap d v).toAdd) :
    s.qSection.imageSpace (QK F) =
      LinearMap.range (s.duality.symm.toLinearEquiv.toLinearMap.comp p.toLinearMap.dualMap) := by
  let j : (naturalAction d).dual.IntertwiningMap s.qAction :=
    s.duality.symm.toIntertwiningMap.comp (OneCohomology.dualIntertwining p)
  change s.qSection.imageSpace (QK F) = j.toLinearMap.range
  apply le_antisymm
  · intro y hy
    obtain ⟨q, hq, rfl⟩ := (s.qSection.mem_imageSpace_iff _ _).mp hy
    have hann : s.duality (s.qSection.coordinates q).toAdd ∈ p.toLinearMap.ker.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      obtain ⟨v, hv⟩ := s.uSection.onto (Multiplicative.ofAdd x)
      have hv' : (s.uSection.coordinates v).toAdd = x := congrArg Multiplicative.toAdd hv
      have hv0 : (v : G) ∈ d.U₀ := by
        have hz : (naturalMap d v).toAdd = 0 := by rw [← hcoord, hv']; exact hx
        exact (d.mem_U₀ v).mpr hz
      rw [← hv']
      apply (s.functional_kernel q v).mpr
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact ((QK_centralizes_fixed d hq) v hv0).symm
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective p.toLinearMap hp] at hann
    obtain ⟨a, ha⟩ := hann
    refine ⟨a, ?_⟩
    change s.duality.symm (p.toLinearMap.dualMap a) = _
    rw [ha, s.duality.symm_apply_apply]
  · let A : Submodule (ZMod 2) (Module.Dual (ZMod 2) SL2FourNatural.V) :=
      (s.qSection.imageSpace (QK F)).comap j.toLinearMap
    have hgen : Coinvariants.ker SL2FourNatural.naturalRepresentation.dual = ⊤ := by
      apply OneCohomology.commutator_dual_eq_top
      apply bot_unique
      intro v hv
      exact SL2FourNatural.natural_fixed_eq_zero v hv
    have hle : Coinvariants.ker SL2FourNatural.naturalRepresentation.dual ≤ A := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, a⟩, rfl⟩
      obtain ⟨k, hk⟩ := d.alternatingActor_lift g
      obtain ⟨q, hq⟩ := s.qSection.onto (Multiplicative.ofAdd (j a))
      let r : F.H.pCoreIn 2 :=
        (⟨(k.val : G) * q * (k.val : G)⁻¹,
          (mem_normalizer_iff.mp (s.qSection.normalized k.val.property) q).mp q.property⟩ :
          F.H.pCoreIn 2) * q⁻¹
      have hr : (r : G) ∈ QK F := by
        apply (le_sup_left : ⁅F.H.pCoreIn 2, K F⁆ ≤ QK F)
        rw [commutator_comm]
        exact commutator_mem_commutator k.property q.property
      change j (SL2FourNatural.naturalRepresentation.dual g a - a) ∈ s.qSection.imageSpace (QK F)
      apply (s.qSection.mem_imageSpace_iff _ _).mpr
      refine ⟨r, hr, ?_⟩
      change (s.qSection.coordinates (_ * q⁻¹)).toAdd = _
      rw [map_mul, map_inv]
      rw [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
      rw [s.qSection.equivariant k.val q, hq, map_sub]
      exact congrArg (fun z => z - j a)
        ((LinearMap.congr_fun (j.isIntertwining' k.val) a).symm.trans
          (congrArg j (natural_dual_on_lift d k.val g hk a)))
    rintro _ ⟨a, rfl⟩
    exact hle (hgen ▸ Submodule.mem_top)

/-- Coordinates on the literal Q_K section, with the original functional kernels. -/
theorem exists_qKDualCoordinates (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    Nonempty (QKDualCoordinates d) := by
  obtain ⟨p, hp, hcoord⟩ := exists_natural_projection d hc s hcomm
  let j : (naturalAction d).dual.IntertwiningMap s.qAction :=
    s.duality.symm.toIntertwiningMap.comp (OneCohomology.dualIntertwining p)
  have hj : Function.Injective j := s.duality.symm.toLinearEquiv.injective.comp
    (LinearMap.dualMap_injective_of_surjective hp)
  have him : s.qSection.imageSpace (QK F) = j.toLinearMap.range :=
    qK_image_eq_dual_range d s p hp hcoord
  have hC : F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) = C F :=
    q_centralizer_eq_h_centralizer d hc
  have hmem (q : F.H.pCoreIn 2) :
      (s.qSection.coordinates q).toAdd ∈ j.toLinearMap.range ↔ (q : G) ∈ QK F := by
    rw [← him]
    exact imageSpace_mem_of_kernel_le s (QK F) (hC ▸ le_sup_right) q
  have hn : F.H ≤ normalizer (QK F : Set G) := by
    apply le_normalizer_iff.mpr
    intro h hh q hq
    let q₀ : F.H.pCoreIn 2 := ⟨q, QK_le_QH d hc hq⟩
    let q₁ : F.H.pCoreIn 2 := ⟨h * q * h⁻¹,
      (mem_normalizer_iff.mp (s.qSection.normalized hh) q).mp q₀.property⟩
    apply (hmem q₁).mp
    obtain ⟨a, ha⟩ := (hmem q₀).mpr hq
    refine ⟨(naturalAction d).dual ⟨h, hh⟩ a, ?_⟩
    change j ((naturalAction d).dual ⟨h, hh⟩ a) = (s.qSection.coordinates q₁).toAdd
    rw [s.qSection.equivariant ⟨h, hh⟩ q₀]
    exact (LinearMap.congr_fun (j.isIntertwining' ⟨h, hh⟩) a).trans
      (congrArg (s.qAction ⟨h, hh⟩) ha)
  let e := LinearEquiv.ofInjective j.toLinearMap hj
  let f : QK F →* Multiplicative j.toLinearMap.range := {
    toFun q := Multiplicative.ofAdd
      ⟨(s.qSection.coordinates ⟨q, QK_le_QH d hc q.property⟩).toAdd,
        (hmem ⟨q, QK_le_QH d hc q.property⟩).mpr q.property⟩
    map_one' := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_one s.qSection.coordinates)
    map_mul' q r := by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (map_mul s.qSection.coordinates
        ⟨q, QK_le_QH d hc q.property⟩ ⟨r, QK_le_QH d hc r.property⟩) }
  let f₀ : QK F →* Multiplicative (Module.Dual (ZMod 2) SL2FourNatural.V) :=
    e.symm.toAddEquiv.toMultiplicative.toMonoidHom.comp f
  have hf (q : QK F) : j (f₀ q).toAdd =
      (s.qSection.coordinates ⟨q, QK_le_QH d hc q.property⟩).toAdd := by
    exact LinearEquiv.ofInjective_symm_apply j.toLinearMap (h := hj) (f q).toAdd
  have honto : Function.Surjective f₀ := by
    intro a
    obtain ⟨q, hq⟩ := s.qSection.onto (Multiplicative.ofAdd (j a.toAdd))
    have hqK : (q : G) ∈ QK F := (hmem q).mp ⟨a.toAdd, by rw [hq]; rfl⟩
    refine ⟨⟨q, hqK⟩, Multiplicative.toAdd.injective (hj ?_)⟩
    rw [hf]
    exact congrArg Multiplicative.toAdd hq
  have hker : f₀.ker = (C F).subgroupOf (QK F) := by
    ext q
    change f₀ q = 1 ↔ (q : G) ∈ C F
    have he : f₀ q = 1 ↔ s.qSection.coordinates ⟨q, QK_le_QH d hc q.property⟩ = 1 := by
      change (f₀ q).toAdd = 0 ↔ (s.qSection.coordinates _).toAdd = 0
      rw [← hf]
      exact (show j (f₀ q).toAdd = j 0 ↔ (f₀ q).toAdd = 0 from hj.eq_iff).symm.trans
        (by rw [show j 0 = 0 from j.toLinearMap.map_zero])
    rw [he, s.qSection.coordinates_eq_one_iff, hC]
  let b : BinaryConjugationSection F.H (QK F) (C F) (naturalAction d).dual := {
    section_le := (QK_le_QH d hc).trans (pCoreIn_le 2 F.H)
    kernel_le := le_sup_right
    normalized := hn
    coordinates := f₀
    onto := honto
    kernel_eq := hker
    equivariant h q := by
      apply hj
      rw [hf]
      calc
        _ = s.qAction h (s.qSection.coordinates ⟨q, QK_le_QH d hc q.property⟩).toAdd :=
          s.qSection.equivariant h ⟨q, QK_le_QH d hc q.property⟩
        _ = s.qAction h (j (f₀ q).toAdd) := congrArg (s.qAction h) (hf q).symm
        _ = _ := (LinearMap.congr_fun (j.isIntertwining' h) (f₀ q).toAdd).symm }
  refine ⟨⟨b, ?_⟩⟩
  intro q v
  have he : s.duality (s.qSection.coordinates ⟨q, QK_le_QH d hc q.property⟩).toAdd
      (s.uSection.coordinates v).toAdd = (f₀ q).toAdd ((naturalMap d v).toAdd) := by
    rw [← hf]
    change s.duality (s.duality.symm (p.toLinearMap.dualMap (f₀ q).toAdd)) _ = _
    rw [s.duality.apply_symm_apply]
    change (f₀ q).toAdd (p (s.uSection.coordinates v).toAdd) = _
    rw [hcoord]
    rfl
  exact he ▸ s.functional_kernel ⟨q, QK_le_QH d hc q.property⟩ v

/-- The natural annihilator corresponds to the literal centralizer of U₀ in Q_H. -/
theorem qK_eq_core_centralizer_fixed (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    QK F = F.H.pCoreIn 2 ⊓ centralizer (d.U₀ : Set G) := by
  apply le_antisymm (le_inf (QK_le_QH d hc) (QK_centralizes_fixed d))
  intro q hq
  obtain ⟨p, hp, hcoord⟩ := exists_natural_projection d hc s hcomm
  have hann : s.duality (s.qSection.coordinates ⟨q, hq.1⟩).toAdd ∈
      p.toLinearMap.ker.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    obtain ⟨v, hv⟩ := s.uSection.onto (Multiplicative.ofAdd x)
    have hv' : (s.uSection.coordinates v).toAdd = x := congrArg Multiplicative.toAdd hv
    have hv0 : (v : G) ∈ d.U₀ := by
      apply (d.mem_U₀ v).mpr
      change d.projection (d.conjugationSection.coordinates v).toAdd = 0
      rw [← hcoord, hv']
      exact hx
    rw [← hv']
    apply (s.functional_kernel ⟨q, hq.1⟩ v).mpr
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hq.2 v hv0).symm
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective p.toLinearMap hp] at hann
  obtain ⟨a, ha⟩ := hann
  apply (imageSpace_mem_of_kernel_le s (QK F)
    ((q_centralizer_eq_h_centralizer d hc) ▸ le_sup_right) ⟨q, hq.1⟩).mp
  rw [qK_image_eq_dual_range d s p hp hcoord]
  refine ⟨a, ?_⟩
  change s.duality.symm (p.toLinearMap.dualMap a) = _
  rw [ha, s.duality.symm_apply_apply]

/-- The other annihilator is precisely U₀, even before U₀=V₁ is known. -/
theorem u_centralizer_qK (b : QKDualCoordinates d) :
    F.U ⊓ centralizer (QK F : Set G) = d.U₀ := by
  apply le_antisymm
  · intro u hu
    apply (d.mem_U₀ ⟨u, hu.1⟩).mpr
    apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp
    intro a
    obtain ⟨q, hq⟩ := b.qSection.onto (Multiplicative.ofAdd a)
    have he := (b.functional_kernel q ⟨u, hu.1⟩).mpr
      (commutatorElement_eq_one_iff_mul_comm.mpr (hu.2 q q.property))
    rw [hq] at he
    exact he
  · exact le_inf d.U₀_le_U (le_centralizer_iff.mp (QK_centralizes_fixed d))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting
