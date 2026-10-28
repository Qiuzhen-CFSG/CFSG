module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorExchange
public import Theory.Representation.OrthogonalFourPlusMatrix.SplitCartan

/-!
# Compatible coordinates for the original tensor and Cartan

Diagonalize the specified odd Cartan and the original orbit Sylow inside
one determinant marking. The same inner coordinate change on the matrix
space retains both original component inclusions, the full two-core kernel,
and the seed action. A nonzero original Sylow-fixed seed vector is an
upper matrix-unit vector in these coordinates. Since H fixes that vector,
its prescribed Hall B lies in the inverse diagonal. Its known order
makes this the full inverse diagonal and proves B = C_C(Omega_1 Z(T)).

The exchanger action module uses precisely these coordinates and this B.
Source: Aschbacher--Smith 9.1.2(5), 9.2.7 and 10.2.3,
printed pp.729,731--732,745, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 HallGeometry
open ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance tensorCompatibleCartanSeedElementary : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance tensorCompatibleCartanBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
variable {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
include c hn e ht htn hsep
set_option backward.isDefEq.respectTransparency false

/-- One common quotient and matrix marking for a prescribed original Cartan.
Both factor inclusions refer to the same original exchanger. -/
structure OriginalTensorCartanMarking {t : G} (ht : t ∈ (T : Subgroup G))
    (n : ℕ) (C : Subgroup G) (hCR : C ≤ localOrbit T L) where
  firstEquiv : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)
  secondEquiv : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)
  quotient : localOrbit T L →* SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)
  coordinates : Additive D.seed ≃ₗ[ZMod 2] Mat (F := GaloisField 2 n)
  cartan : C ≃* (GaloisField 2 n)ˣ × (GaloisField 2 n)ˣ
  surjective : Function.Surjective quotient
  kernel : quotient.ker = pCore 2 (localOrbit T L)
  first : ∀ l : L, quotient ⟨l,le_componentOrbit L T l.property⟩ =
    (firstEquiv (QuotientGroup.mk' _ l),1)
  second : ∀ l : L, quotient (originalConjugateOrbitInclusion ht l) =
    (1,secondEquiv (QuotientGroup.mk' _ l))
  sylow : ((T : Subgroup G).subgroupOf (localOrbit T L)).map quotient =
    (Matrix.SpecialLinearGroup.upperUnipotent (GaloisField 2 n)).prod
      (Matrix.SpecialLinearGroup.upperUnipotent (GaloisField 2 n))
  intertwines : ∀ g v, coordinates (originalSeedAction D g v) =
    representation (quotient g) (coordinates v)
  diagonal : ∀ x : C, quotient ⟨x,hCR x.property⟩ =
    (Matrix.SpecialLinearGroup.diag2 ((cartan x).1 : GaloisField 2 n) (Units.ne_zero _),
      Matrix.SpecialLinearGroup.diag2 ((cartan x).2 : GaloisField 2 n) (Units.ne_zero _))

/-- Simultaneous tensor and split-Cartan coordinates on the specified C.
The two component inclusions use the same original exchanger t. -/
theorem original_even_same_cartan_coordinates
    (C : Subgroup G) (hC : C ≤ sourceOrbitBorel T L)
    (hodd : Odd (Nat.card C))
    (hcard : Nat.card C = Nat.card ((GaloisField 2 n)ˣ × (GaloisField 2 n)ˣ)) :
    Nonempty (OriginalTensorCartanMarking D ht n C
      ((hC.trans (map_subtype_le _)).trans inf_le_left)) := by
  let F := GaloisField 2 n
  let R := localOrbit T L
  have hCR : C ≤ R := (hC.trans (map_subtype_le _)).trans inf_le_left
  let i : C →* R := inclusion hCR
  obtain ⟨q₀,hq₀,hk₀,hl₀,hr₀,α,f₀,hf₀⟩ :=
    original_even_seed_determinant D c n hn e ht htn hsep
  let m := NaturalTensor.marking α
  let r := m.toMonoidHom.comp q₀
  have hr : Function.Surjective r := m.surjective.comp hq₀
  have hk : r.ker = pCore 2 R := by
    ext x
    change m (q₀ x) = 1 ↔ x ∈ pCore 2 R
    rw [m.map_eq_one_iff]
    exact Iff.of_eq (congrArg (fun K : Subgroup R => x ∈ K) hk₀)
  let qC := r.comp i
  have hi : Function.Injective qC := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxk : i x ∈ pCore 2 R := hk ▸ hx
    obtain ⟨k,hkp⟩ := (pCore_isPGroup (p := 2) (G := R)) ⟨i x,hxk⟩
    have hpow : x^(2^k) = 1 := by
      apply inclusion_injective hCR
      rw [map_pow,map_one]
      exact congrArg Subtype.val hkp
    exact mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((hodd.of_dvd_nat (orderOf_dvd_natCard x)).coprime_two_right.pow_right k)
        dvd_rfl (orderOf_dvd_of_pow_eq_one hpow)))
  obtain ⟨S,hS⟩ := source_orbit_sylow_intersection D
  let Sq := S.mapSurjective hr
  have hCN : ∀ x : C, i x ∈ normalizer (S : Set R) := by
    intro x
    rw [←source_orbit_sylow_normalizer_eq S hS]
    exact (hC.trans (map_subtype_le _)) x.property
  have hN : qC.range ≤ normalizer (Sq : Set (SL(2,F) × SL(2,F))) := by
    rintro _ ⟨x,rfl⟩
    exact (le_normalizer_map r) ⟨i x,hCN x,rfl⟩
  have hor : Odd (Nat.card qC.range) := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    exact hodd
  obtain ⟨a,b,dq,hSq,hdq⟩ :=
    Matrix.SpecialLinearGroup.pair_sylow_odd_subgroup_diagonal_coordinates Sq qC.range hN hor
  let v := (MulAut.conj a).prodCongr (MulAut.conj b)
  let q := v.toMonoidHom.comp r
  let dc := dq.comp qC.rangeRestrict
  have hdiag (x : C) : q (i x) =
      (Matrix.SpecialLinearGroup.diag2 ((dc x).1 : F) (Units.ne_zero _),
        Matrix.SpecialLinearGroup.diag2 ((dc x).2 : F) (Units.ne_zero _)) := hdq (qC.rangeRestrict x)
  have hdi : Function.Injective dc := by
    intro x y hxy
    apply hi
    apply v.injective
    change q (i x) = q (i y)
    rw [hdiag,hdiag,hxy]
  let d := MulEquiv.ofBijective dc ((Nat.bijective_iff_injective_and_card dc).mpr ⟨hdi,hcard⟩)
  let f := f₀.trans ((matrixAction (a,b)).restrictScalars (ZMod 2))
  refine ⟨⟨e.trans (α.symm.trans (MulAut.conj a)),
    e.trans (NaturalTensor.dual.trans (MulAut.conj b)),q,f,d,
    v.surjective.comp hr,?_,?_,?_,?_,?_,hdiag⟩⟩
  · ext x
    change v (r x) = 1 ↔ x ∈ pCore 2 R
    rw [v.map_eq_one_iff]
    exact Iff.of_eq (congrArg (fun K : Subgroup R => x ∈ K) hk)
  · intro l
    change v (m (q₀ _)) = _
    rw [hl₀]
    refine Prod.ext ?_ ?_
    · rfl
    · change (MulAut.conj b) (NaturalTensor.dual 1) = 1
      rw [map_one,map_one]
  · intro l
    change v (m (q₀ _)) = _
    rw [hr₀]
    refine Prod.ext ?_ ?_
    · change (MulAut.conj a) (α.symm 1) = 1
      rw [map_one,map_one]
    · rfl
  · change ((T : Subgroup G).subgroupOf R).map (v.toMonoidHom.comp r) = _
    rw [←map_map,←hS]
    exact hSq
  · intro g w
    change matrixAction (a,b) (f₀ (originalSeedAction D g w)) =
      representation (v (r g)) (matrixAction (a,b) (f₀ w))
    rw [hf₀]
    exact SplitCartan.inner_coordinates (a,b) (r g) (f₀ w)


/-- The original B fills the inverse diagonal in the same Cartan marking.
Its first coordinate is an actual multiplicative equivalence. -/
theorem original_even_same_cartan_hall
    (C : Subgroup G) (hCR : C ≤ localOrbit T L) (hBC : B.map H.subtype ≤ C)
    (k : OriginalTensorCartanMarking D ht n C hCR) :
    ∃ χ : B ≃* (GaloisField 2 n)ˣ,
      (∀ b : B, k.cartan ⟨(b:G),hBC (mem_map_of_mem H.subtype b.property)⟩ = (χ b,(χ b)⁻¹)) ∧
      (∀ x : C, (x:G) ∈ B.map H.subtype ↔ (k.cartan x).2 = (k.cartan x).1⁻¹) ∧
      C ⊓ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) =
        B.map H.subtype := by
  let F := GaloisField 2 n
  let j : B →* C := (H.subtype.comp B.subtype).codRestrict _
    (fun b => hBC (mem_map_of_mem H.subtype b.property))
  have hji : Function.Injective j := by
    intro b d hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : C => (x:G)) hh
  obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (original_even_seed_fixed_ne_bot D c n hn e ht htn hsep)
  let v : Additive D.seed := Additive.ofMul ⟨(z:G),z.property.1⟩
  have hv : k.coordinates v ≠ 0 := by
    intro hh
    have he := k.coordinates.injective (hh.trans k.coordinates.map_zero.symm)
    exact hz (Subtype.ext (congrArg (fun w : Additive D.seed => (w.toMul:G)) he))
  have hshape : k.coordinates v = SplitCartan.upperPoint (k.coordinates v 0 1) := by
    apply SplitCartan.upper_fixed
    intro a ha
    have ha' := k.sylow.symm ▸ ha
    obtain ⟨g,hg,rfl⟩ := ha'
    change representation (k.quotient g) (k.coordinates v) = k.coordinates v
    rw [←k.intertwines]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    change (g:G)*(z:G)*(g:G)⁻¹ = (z:G)
    rw [z.property.2 (g:G) hg,mul_inv_cancel_right]
  have hscalar : k.coordinates v 0 1 ≠ 0 := by
    intro hh
    apply hv
    rw [hshape,hh]
    ext i l
    fin_cases i <;> fin_cases l <;> rfl
  have hZ := original_even_seed_fixed_le_omegaCenter D c n hn e ht htn hsep z.property
  have hH : H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp c.central)
  have hanti (x : C) (hfix : (x:G)*(z:G)*(x:G)⁻¹ = (z:G)) :
      (k.cartan x).2 = (k.cartan x).1⁻¹ := by
    apply (SplitCartan.diagonal_fixed_iff _ _ hscalar).mp
    rw [←hshape,←k.diagonal x]
    change representation (k.quotient ⟨x,hCR x.property⟩) (k.coordinates v) = k.coordinates v
    rw [←k.intertwines]
    congr 1
    apply Additive.toMul.injective
    exact Subtype.ext hfix
  have hB (b : B) : (k.cartan (j b)).2 = (k.cartan (j b)).1⁻¹ :=
    hanti (j b) (by
      change (b:G)*(z:G)*(b:G)⁻¹ = (z:G)
      rw [←hH b.val.property _ hZ,mul_inv_cancel_right])
  let χ₀ := (MonoidHom.fst Fˣ Fˣ).comp (k.cartan.toMonoidHom.comp j)
  have hχi : Function.Injective χ₀ := by
    intro b d hh
    apply hji
    apply k.cartan.injective
    apply Prod.ext hh
    change (k.cartan (j b)).2 = (k.cartan (j d)).2
    rw [hB,hB]
    exact congrArg Inv.inv hh
  have hχc : Nat.card B = Nat.card Fˣ := by
    rw [original_even_hall_card D c n hn e ht htn hsep,Nat.card_units,
      GaloisField.card 2 n (by omega)]
  let χ := MulEquiv.ofBijective χ₀ ((Nat.bijective_iff_injective_and_card χ₀).mpr ⟨hχi,hχc⟩)
  have hmark (b : B) : k.cartan (j b) = (χ b,(χ b)⁻¹) := Prod.ext rfl (hB b)
  have hmem (x : C) : (x:G) ∈ B.map H.subtype ↔ (k.cartan x).2 = (k.cartan x).1⁻¹ := by
    constructor
    · rintro ⟨b,hb,he⟩
      have hx : j ⟨b,hb⟩ = x := Subtype.ext he
      rw [←hx]
      exact hB ⟨b,hb⟩
    · intro hx
      obtain ⟨b,hb⟩ := χ.surjective (k.cartan x).1
      have he : j b = x := k.cartan.injective (by rw [hmark,hb]; exact Prod.ext rfl hx.symm)
      exact (congrArg (fun x : C => (x:G)) he) ▸ mem_map_of_mem H.subtype b.property
  refine ⟨χ,hmark,hmem,?_⟩
  apply le_antisymm
  · intro x hx
    apply (hmem ⟨x,hx.1⟩).mpr
    apply hanti
    rw [←hx.2 _ hZ,mul_inv_cancel_right]
  · intro x hx
    exact ⟨hBC hx,hH ((map_subtype_le B) hx)⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
