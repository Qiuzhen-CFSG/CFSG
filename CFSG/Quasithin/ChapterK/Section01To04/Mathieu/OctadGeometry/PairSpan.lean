module

public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.OctadGeometry.Reduction
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryPermutation.SymmetricEightTransvections

/-!
# The orthogonal quotient and the octad pair span

The actual quotient U/V5 is marked equivariantly as the natural binary
permutation module on the octad, where V5 is `codeOctadMoved O`. A fixed-point-free
involution on eight points has displacement rank at least two: the natural
S8-action is faithful, and a rank-one involution in a faithful binary S8-module
must be a transposition. The literal quotient map kills the four-dimensional
displacement of z. Rank-nullity on the pair span therefore gives dimension at
least six. Applying the checked reduction gives the common fixed and commutator
space of dimension six and dual fixed codimension six; it also forces the
quotient displacement to have dimension exactly two.

The explicit inputs are the genuine equivariant quotient identification from
H.16.2(3), the dimension and elementary-abelian conclusions from H.16.2(6),
and, for the equalities, the fixed-space formula from H.16.2(7). Point-freeness
on the octad remains an explicit input to be discharged by the centralizer
incidence argument. No displacement dimension is assumed. The earlier-source
inputs and point-freeness must be discharged in the source-theorem assembly.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), H.16.2,
printed pp.402--403, and K.4.3(5--6), printed pp.458--459
(PDF pp.469--470), refs/quasithin.pdf.
-/

public section

open Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open CFSG.Quasithin.ChapterH.Section13To16
open scoped IsMulCommutative
open MathieuCode

namespace CFSG.Quasithin.ChapterK.Mathieu.OctadGeometry.PairSpan

private theorem natural_rank_lower {Ω : Type*} [Fintype Ω] (hc : Fintype.card Ω = 8)
    (p : Equiv.Perm Ω) (hp2 : p ^ 2 = 1) (hf : ∀ i, p i ≠ i) :
    2 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (displacement (BinaryPermutation.naturalRepresentation Ω) p)) := by
  classical
  let e := (Fintype.equivFinOfCardEq hc).permCongrHom
  let ρ := BinaryPermutation.naturalRepresentation Ω
  let φ : Equiv.Perm Ω →* (BinaryPermutation.natural Ω ≃ₗ[ZMod 2]
      BinaryPermutation.natural Ω) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).toMonoidHom.comp ρ.asGroupHom
  have hi : Function.Injective φ := fun a b h =>
    BinaryPermutation.naturalRepresentation_injective Ω (by omega)
      (congrArg LinearEquiv.toLinearMap h)
  have hp1 : p ≠ 1 := by
    intro he
    let i := (Fintype.equivFinOfCardEq hc).symm 0
    exact hf i (by rw [he]; rfl)
  by_contra hn
  change ¬ 2 ≤ Module.finrank (ZMod 2) (LinearMap.range (displacement ρ p)) at hn
  have ht : φ p ∈ LinearEquiv.transvections (ZMod 2) (BinaryPermutation.natural Ω) :=
    SymmetricEightTransvections.Linear.of_small_displacement (φ p) (by
      change Module.finrank (ZMod 2) (LinearMap.range (displacement ρ p)) ≤ 1
      omega)
  have hs := SymmetricEightTransvections.isSwap_of_transvection
    (φ.comp e.symm.toMonoidHom) (hi.comp e.symm.injective) (e p)
    (fun h => hp1 (e.injective (h.trans e.map_one.symm)))
    (by rw [← map_pow, hp2, map_one])
    (by simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply] using ht)
  have hfree (i : Fin 8) : (e p) i ≠ i := by
    intro he
    apply hf ((Fintype.equivFinOfCardEq hc).symm i)
    exact (Fintype.equivFinOfCardEq hc).injective
      (he.trans ((Fintype.equivFinOfCardEq hc).apply_symm_apply i).symm)
  have hu : (e p).support = Finset.univ := by
    ext i
    simp [Equiv.Perm.mem_support, hfree]
  have hh := Equiv.Perm.card_support_eq_two.mpr hs
  simp [hu] at hh

private theorem octad_fixed_points (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1) :
    ∀ i : Fin 24, z • i = i ↔ i ∈ O.val := by
  have hzfix := (mem_octadPointwiseKernel O z).mp
    (show z ∈ octadPointwiseKernel O by rwa [← octad_core_map_eq_pointwise O])
  have hc : O.val.Nonempty := Finset.card_pos.mp (by rw [m24Blocks_card _ O.property]; decide)
  obtain ⟨i, hi⟩ := hc
  obtain ⟨P, _, hP⟩ := fixed_involution_octad z (octad_involution_order O z hz hz1)
    ⟨i, hzfix i hi⟩
  have he : O.val = P.val := Finset.eq_of_subset_of_card_le
    (fun j hj => (hP j).mp (hzfix j hj)) (by
      rw [m24Blocks_card _ P.property, m24Blocks_card _ O.property])
  simpa only [he] using hP

private theorem octad_centralizer_stabilizes (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hD : IsElementaryAbelian 2 (codeOctadInvolutionCentralizer O z)) :
    codeOctadInvolutionCentralizer O z ≤ octadStabilizer O := by
  let _ := hD
  intro d hd
  have hcomm : Commute z d := congrArg Subtype.val
    (mul_comm (⟨z, octad_involution_mem_centralizer O z⟩ :
      codeOctadInvolutionCentralizer O z) ⟨d, hd⟩)
  apply MulAction.mem_stabilizer_finset'.mpr
  intro i hi
  apply (octad_fixed_points O z hz hz1 _).mp
  rw [← mul_smul, hcomm.eq, mul_smul, (octad_fixed_points O z hz hz1 i).mpr hi]

private theorem pair_rank_bound {k V W : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    (q : V →ₗ[k] W) (A B : Submodule k V) (hA : A ≤ q.ker) :
    Module.finrank k A + Module.finrank k (B.map q) ≤ Module.finrank k (A ⊔ B : Submodule k V) := by
  let S := A ⊔ B
  let f := q.domRestrict S
  have hker : A.comap S.subtype ≤ f.ker := fun v hv => hA hv
  have hdimA : Module.finrank k A ≤ Module.finrank k f.ker := by
    have h := Submodule.finrank_mono hker
    rw [(Submodule.comapSubtypeEquivOfLe (show A ≤ S from le_sup_left)).finrank_eq] at h
    exact h
  have him : B.map q ≤ f.range := by
    rw [LinearMap.range_domRestrict]
    exact Submodule.map_mono le_sup_right
  have hdimB := Submodule.finrank_mono him
  have hsum := f.finrank_range_add_finrank_ker
  change Module.finrank k A + Module.finrank k (B.map q) ≤ Module.finrank k S
  omega

private theorem octad_pair_estimates (O : Octad) (z d : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hdim : Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hd : d ∈ codeOctadInvolutionCentralizer O z)
    (hD : IsElementaryAbelian 2 (codeOctadInvolutionCentralizer O z))
    (E : (Code ⧸ codeOctadMoved O) ≃ₗ[ZMod 2] BinaryPermutation.natural O.val)
    (hE : ∀ (g : octadStabilizer O) (v : Code),
      E ((codeOctadMoved O).mkQ (codeRepresentation g.val v)) =
        BinaryPermutation.naturalRepresentation O.val (CocodeOctad.coordinateAction O g)
          (E ((codeOctadMoved O).mkQ v)))
    (hfree : ∀ i ∈ O.val, d • i ≠ i) :
    2 ≤ Module.finrank (ZMod 2)
        ((LinearMap.range (displacement codeRepresentation d)).map (codeOctadMoved O).mkQ) ∧
      4 + Module.finrank (ZMod 2)
        ((LinearMap.range (displacement codeRepresentation d)).map (codeOctadMoved O).mkQ) ≤
      Module.finrank (ZMod 2)
        (LinearMap.range (displacement codeRepresentation z) ⊔
          LinearMap.range (displacement codeRepresentation d) : Submodule (ZMod 2) Code) := by
  let q := E.toLinearMap.comp (codeOctadMoved O).mkQ
  let a : octadStabilizer O := ⟨d, octad_centralizer_stabilizes O z hz hz1 hD hd⟩
  let p := CocodeOctad.coordinateAction O a
  let _ := hD
  have hp2 : p ^ 2 = 1 := by
    have hd2 : a ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) d hd)
    exact (map_pow (CocodeOctad.coordinateAction O) a 2).symm.trans
      ((congrArg (CocodeOctad.coordinateAction O) hd2).trans (map_one _))
  have hpf (i : O.val) : p i ≠ i := by
    intro he
    apply hfree i.val i.property
    simpa only [p, a, CocodeOctad.coordinateAction_apply, Subgroup.smul_def,
      Equiv.Perm.smul_def] using congrArg Subtype.val he
  have hlower := natural_rank_lower
    (show Fintype.card O.val = 8 by simp [m24Blocks_card _ O.property]) p hp2 hpf
  have hq : Function.Surjective q := E.surjective.comp (codeOctadMoved O).mkQ_surjective
  have he (v : Code) : q (displacement codeRepresentation d v) =
      displacement (BinaryPermutation.naturalRepresentation O.val) p (q v) := by
    change q (codeRepresentation d v - v) =
      BinaryPermutation.naturalRepresentation O.val p (q v) - q v
    rw [map_sub]
    exact congrArg (fun x => x - q v) (hE a v)
  have him : (LinearMap.range (displacement codeRepresentation d)).map q =
      LinearMap.range (displacement (BinaryPermutation.naturalRepresentation O.val) p) := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨q v, (he v).symm⟩
    · rintro _ ⟨w, rfl⟩
      obtain ⟨v, rfl⟩ := hq w
      exact ⟨_, ⟨v, rfl⟩, he v⟩
  have hA : LinearMap.range (displacement codeRepresentation z) ≤ q.ker := by
    intro v hv
    rw [octad_involution_displacement O z hz hz1 hdim] at hv
    change E ((codeOctadMoved O).mkQ v) = 0
    rw [(codeOctadMoved O).mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hv.1,
      map_zero]
  have hb := pair_rank_bound q (LinearMap.range (displacement codeRepresentation z))
    (LinearMap.range (displacement codeRepresentation d)) hA
  have hdimA : Module.finrank (ZMod 2)
      (LinearMap.range (displacement codeRepresentation z)) = 4 := by
    rw [octad_involution_displacement O z hz hz1 hdim, hdim]
  have hdimq : Module.finrank (ZMod 2)
      ((LinearMap.range (displacement codeRepresentation d)).map q) =
      Module.finrank (ZMod 2)
        ((LinearMap.range (displacement codeRepresentation d)).map (codeOctadMoved O).mkQ) := by
    rw [show q = E.toLinearMap.comp (codeOctadMoved O).mkQ from rfl,
      Submodule.map_comp, E.finrank_map_eq]
  rw [← him, hdimq] at hlower
  rw [hdimA, hdimq] at hb
  exact ⟨hlower, hb⟩

/-- The two quotient directions add to the four-dimensional displacement of z. -/
theorem octad_pair_span_lower (O : Octad) (z d : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hdim : Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hd : d ∈ codeOctadInvolutionCentralizer O z)
    (hD : IsElementaryAbelian 2 (codeOctadInvolutionCentralizer O z))
    (E : (Code ⧸ codeOctadMoved O) ≃ₗ[ZMod 2] BinaryPermutation.natural O.val)
    (hE : ∀ (g : octadStabilizer O) (v : Code),
      E ((codeOctadMoved O).mkQ (codeRepresentation g.val v)) =
        BinaryPermutation.naturalRepresentation O.val (CocodeOctad.coordinateAction O g)
          (E ((codeOctadMoved O).mkQ v)))
    (hfree : ∀ i ∈ O.val, d • i ≠ i) :
    6 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (displacement codeRepresentation z) ⊔
        LinearMap.range (displacement codeRepresentation d) : Submodule (ZMod 2) Code) := by
  obtain ⟨hlo, hsum⟩ := octad_pair_estimates O z d hz hz1 hdim hd hD E hE hfree
  omega

/-- K.4.3(5--6), conditional on the actual H.16 quotient marking and point freeness. -/
theorem octad_pair_spaces (O : Octad) (z d : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hdim : Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hd : d ∈ codeOctadInvolutionCentralizer O z)
    (hD : IsElementaryAbelian 2 (codeOctadInvolutionCentralizer O z))
    (E : (Code ⧸ codeOctadMoved O) ≃ₗ[ZMod 2] BinaryPermutation.natural O.val)
    (hE : ∀ (g : octadStabilizer O) (v : Code),
      E ((codeOctadMoved O).mkQ (codeRepresentation g.val v)) =
        BinaryPermutation.naturalRepresentation O.val (CocodeOctad.coordinateAction O g)
          (E ((codeOctadMoved O).mkQ v)))
    (hfree : ∀ i ∈ O.val, d • i ≠ i)
    (hdz : d ∉ Subgroup.zpowers z)
    (hfixed : ∀ B : Subgroup M24, z ∈ B → B ≤ codeOctadInvolutionCentralizer O z →
      Module.finrank (ZMod 2) (fixedSpace codeRepresentation B) = 8 - rank B) :
    fixedSpace codeRepresentation (octadPair z d) =
        subspaceCommutator codeRepresentation ⊤ (octadPair z d) ∧
      Module.finrank (ZMod 2)
        (LinearMap.range (displacement codeRepresentation z) ⊔
          LinearMap.range (displacement codeRepresentation d) : Submodule (ZMod 2) Code) = 6 ∧
      fixedCodim codeRepresentation.dual (octadPair z d) = 6 := by
  exact octad_pair_spaces_of_span_lower O z d hz hz1 hdim hd hdz hD hfixed
    (octad_pair_span_lower O z d hz hz1 hdim hd hD E hE hfree)

/-- The displacement in the literal U/V5 quotient has dimension exactly two. -/
theorem octad_pair_quotient_displacement (O : Octad) (z d : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hdim : Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hd : d ∈ codeOctadInvolutionCentralizer O z)
    (hD : IsElementaryAbelian 2 (codeOctadInvolutionCentralizer O z))
    (E : (Code ⧸ codeOctadMoved O) ≃ₗ[ZMod 2] BinaryPermutation.natural O.val)
    (hE : ∀ (g : octadStabilizer O) (v : Code),
      E ((codeOctadMoved O).mkQ (codeRepresentation g.val v)) =
        BinaryPermutation.naturalRepresentation O.val (CocodeOctad.coordinateAction O g)
          (E ((codeOctadMoved O).mkQ v)))
    (hfree : ∀ i ∈ O.val, d • i ≠ i)
    (hdz : d ∉ Subgroup.zpowers z)
    (hfixed : ∀ B : Subgroup M24, z ∈ B → B ≤ codeOctadInvolutionCentralizer O z →
      Module.finrank (ZMod 2) (fixedSpace codeRepresentation B) = 8 - rank B) :
    Module.finrank (ZMod 2)
      ((LinearMap.range (displacement codeRepresentation d)).map (codeOctadMoved O).mkQ) = 2 := by
  obtain ⟨hlo, hsum⟩ := octad_pair_estimates O z d hz hz1 hdim hd hD E hE hfree
  have hsix := (octad_pair_spaces O z d hz hz1 hdim hd hD E hE hfree hdz hfixed).2.1
  omega

end CFSG.Quasithin.ChapterK.Mathieu.OctadGeometry.PairSpan
