module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideDerivedSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedSource
public import Theory.GroupTheory.ElementaryPairFixedCard
public import Theory.GroupTheory.ElementaryPairQuadratic
public import Theory.Frattini.BinarySquares
/-!
# Cardinality and Frattini subgroup of an outside fixed group

The exchanged elementary factors and central coboundaries give
|C_R(t)|·|Z(R)|=|U|·|C_Z(R)(t)|. In the centerless block this becomes
|C_R(t)|=2^n·|C_Z(R)(t)|. Every square lies in Z(R), so the already proved
fixed-derived equality also identifies the literal ambient Frattini image.
The actual center-action source supplies the remaining coboundary equation.

Source: Aschbacher–Smith, Lemma 2.4.14(2), printed p.533; these are the
exact local group outputs used in the terminal counting argument on p.539.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_outside_fixed_card_mul_of_coboundaries
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (t : G) (htT : t ∈ T) (htS : t ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ht2 : t^2=1)
    (htrace : ∀ z ∈ (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)
        : Subgroup G), Commute t z → ∃ w ∈
        (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)
        : Subgroup G), z=w*(t*w*t⁻¹)⁻¹) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    Nat.card (R ⊓ centralizer ({t}:Set G) : Subgroup G) * Nat.card Z =
      Nat.card (sourceModule (d.block.map d.H.subtype)) *
        Nat.card (Z ⊓ centralizer ({t}:Set G) : Subgroup G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule L
  let V := U.map (MulAut.conj t).toMonoidHom
  let Z := R ⊓ centralizer (R : Set G)
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hK
  have hf := source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique
  have hU : U = twoCore d.H := (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2
  let : IsElementaryAbelian 2 U := hU.symm ▸ (d.core_source hG T hST).2.2.2.1
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  have hgen : U ⊔ V = R := by simpa only [hti] using (hf.2.2.2 t htT htS).1.symm
  have hZ : U ⊓ V = Z := by
    simpa only [hti] using source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique t htT htS
  have hUR : U ≤ R := le_sup_left.trans_eq hgen
  have hVR : V ≤ R := le_sup_right.trans_eq hgen
  have hRU : R ≤ normalizer (U : Set G) :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1.trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  have hRt : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (ht.2.2 htT)
  have hRV : R ≤ normalizer (V : Set G) := by
    have hh := (map_mono (f := (MulAut.conj t).toMonoidHom) hRU).trans
      (U.le_normalizer_map (MulAut.conj t).toMonoidHom)
    rwa [hRt] at hh
  have hder : ⁅R,R⁆ ≤ Z := by
    rw [←hZ]
    apply le_inf
    · rw [←hgen]
      exact commutator_sup_le_of_normalized_derived U V (hVR.trans hRU)
        (by rw [commutator_self_eq_bot_iff.mpr inferInstance];exact bot_le)
    · rw [←hgen,sup_comm U V]
      exact commutator_sup_le_of_normalized_derived V U (hUR.trans hRV)
        (by rw [commutator_self_eq_bot_iff.mpr inferInstance];exact bot_le)
  have ha (x : G) : (MulAut.conj t) ((MulAut.conj t) x)=x := by
    simp only [MulAut.conj_apply]
    have htt : t*t=1 := by simpa only [pow_two] using ht2
    rw [hti]
    calc t*(t*x*t)*t=(t*t)*x*(t*t) := by group
         _=x := by rw [htt,one_mul,mul_one]
  have heq : (MulAut.conj t).toMonoidHom.eqLocus (MonoidHom.id G) = centralizer ({t} : Set G) := by
    ext x
    change t*x*t⁻¹=x ↔ x∈centralizer ({t}:Set G)
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  have hh := elementary_pair_fixed_card_mul R U V Z hgen hRU hZ hder
    (MulAut.conj t) ha rfl (by
      intro z hz hzfix
      have htz : Commute t z := mul_inv_eq_iff_eq_mul.mp hzfix
      exact htrace z hz htz)
  rw [heq] at hh
  exact hh

theorem source_centerless_outside_fixed_card_of_coboundaries
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (t : G) (htT : t ∈ T) (htS : t ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ht2 : t^2=1)
    (htrace : ∀ z ∈ (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)
        : Subgroup G), Commute t z → ∃ w ∈
        (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)
        : Subgroup G), z=w*(t*w*t⁻¹)⁻¹)
    (hcenter : center (d.block.map d.H.subtype)=⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    Nat.card (R ⊓ centralizer ({t}:Set G) : Subgroup G) =
      2^n * Nat.card (Z ⊓ centralizer ({t}:Set G) : Subgroup G) := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let U := sourceModule (d.block.map d.H.subtype)
  let Z := R ⊓ centralizer (R : Set G)
  let I := R ⊓ centralizer ({t}:Set G)
  let J := Z ⊓ centralizer ({t}:Set G)
  have hUcard : Nat.card U=Nat.card Z^2 :=
    source_centerless_elementary_pair_card d hG T hST hsingle hL hM hTM hunique hcenter
  have hZcard : Nat.card Z=2^n := by
    have hh := (source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).2.1
    rwa [distinguishedZ_of_centerless d hcenter] at hh
  have hh : Nat.card I*Nat.card Z=Nat.card U*Nat.card J :=
    source_outside_fixed_card_mul_of_coboundaries d hG T hST hsingle hL hM hTM hunique
      t htT htS ht2 htrace
  change Nat.card I=2^n*Nat.card J
  have hpos : 0<Nat.card Z := Nat.card_pos
  rw [hUcard,hZcard] at hh
  rw [hZcard] at hpos
  nlinarith

theorem source_outside_fixed_frattini_of_coboundaries
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (t : G) (htT : t ∈ T) (htS : t ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ht2 : t^2=1)
    (htrace : ∀ z ∈ (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)
        : Subgroup G), Commute t z → ∃ w ∈
        (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)
        : Subgroup G), z=w*(t*w*t⁻¹)⁻¹) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    let I := R ⊓ centralizer ({t}:Set G)
    (frattini I).map I.subtype=Z ⊓ centralizer ({t}:Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule L
  let V := U.map (MulAut.conj t).toMonoidHom
  let Z := R ⊓ centralizer (R : Set G)
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hK
  have hf := source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique
  have hU : U = twoCore d.H := (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2
  let : IsElementaryAbelian 2 U := hU.symm ▸ (d.core_source hG T hST).2.2.2.1
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  have hgen : U ⊔ V = R := by simpa only [hti] using (hf.2.2.2 t htT htS).1.symm
  have hZ : U ⊓ V = Z := by
    simpa only [hti] using source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique t htT htS
  have hUR : U ≤ R := le_sup_left.trans_eq hgen
  have hVR : V ≤ R := le_sup_right.trans_eq hgen
  have hRU : R ≤ normalizer (U : Set G) :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1.trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  have hRt : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (ht.2.2 htT)
  have hRV : R ≤ normalizer (V : Set G) := by
    have hh := (map_mono (f := (MulAut.conj t).toMonoidHom) hRU).trans
      (U.le_normalizer_map (MulAut.conj t).toMonoidHom)
    rwa [hRt] at hh
  have hder : ⁅R,R⁆ ≤ Z := by
    rw [←hZ]
    apply le_inf
    · rw [←hgen]
      exact commutator_sup_le_of_normalized_derived U V (hVR.trans hRU)
        (by rw [commutator_self_eq_bot_iff.mpr inferInstance];exact bot_le)
    · rw [←hgen,sup_comm U V]
      exact commutator_sup_le_of_normalized_derived V U (hUR.trans hRV)
        (by rw [commutator_self_eq_bot_iff.mpr inferInstance];exact bot_le)
  let I := R ⊓ centralizer ({t}:Set G)
  let J := Z ⊓ centralizer ({t}:Set G)
  have hIT : I≤(T : Subgroup G) := inf_le_left.trans
    ((show R≤S from sSup_le fun _ h=>h.1).trans hST.le)
  have hIp : IsPGroup 2 I := T.isPGroup'.of_injective (inclusion hIT) (inclusion_injective hIT)
  let _ : Fact (IsPGroup 2 I) := ⟨hIp⟩
  have hN : (Z.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    ((le_centralizer_iff.mp (show Z≤centralizer (R:Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _))
  let _ := hN
  let _ : IsElementaryAbelian 2 (R ⧸ Z.subgroupOf R) :=
    elementary_pair_quotient R U V Z hgen hRU hder hN
  have hsquare (r : R) : (r:G)^2∈Z := by
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ Z.subgroupOf R))
      ((QuotientGroup.mk' (Z.subgroupOf R)) r)
    rw [←map_pow] at hh
    exact (QuotientGroup.eq_one_iff (N:=Z.subgroupOf R) (x:=r^2)).mp hh
  have hupper : (frattini I).map I.subtype≤J := by
    rw [map_le_iff_le_comap,hIp.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨hsquare ⟨i,i.property.1⟩,
      (centralizer ({t}:Set G)).pow_mem i.property.2 2⟩
  have hlow := map_mono (f:=I.subtype) (commutator_le_frattini_of_isPGroup (p:=2))
  rw [map_subtype_commutator] at hlow
  have hJ : ⁅I,I⁆=J := source_outside_fixed_derived_of_coboundaries d hG T hST hsingle hL hM
    hTM hunique t htT htS ht2 htrace
  change (frattini I).map I.subtype=J
  rw [hJ] at hlow
  exact le_antisymm hupper hlow

end CFSG.Quasithin.Chapter2.LinearShadows.Single
