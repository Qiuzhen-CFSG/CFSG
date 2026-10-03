module

public import Stellmacher.Recognition.Parrott.SecondCentralizerLocalSylow
public import Stellmacher.Recognition.Parrott.SecondNormalizerTransport
public import Stellmacher.Recognition.Parrott.NormalizerElementaryFusion
public import Stellmacher.Recognition.Parrott.NormalizerElementaryCentralizer

/-!
# Outside-omega involutions in the second centralizer

Put N=N_G(F), K=O₂(N), W=Ω₁(K), and V=C_N(v), with all
subgroups embedded in G. Sylow conjugacy in V moves each involution
outside W into P=T∩C_G(v), preserving nonmembership in K.

Every involution of T outside the original core J fixes eight points of
E=J′. The existing containment of this fixed space in Z(W), also of
order eight, is therefore equality. Since C_N(Z(W))=W, all such
involutions lie in W. Consequently each involution of V outside W has
a V-conjugate in J outside E.

For an involution already in P outside W, its original-core fixed join
is an H-conjugate of F inside V. The final lemma controls the ambient
normalizer of this join when v lies outside its omega center. These
interfaces leave the special centralizer witness to the geometry assembly.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678 and §4, p.682.
-/

open Subgroup
open scoped Pointwise

namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Sylow conjugacy inside V preserves the outside-core condition and lands
in the supplied intersection P. -/
public theorem normalizer_fixed_outside_omega_conjugate_into_sylow
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let V := N ⊓ centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G)
    ∀ l : G, l ∈ V → orderOf l = 2 → l ∉ W →
      ∃ g : V, (g : G) * l * (g : G)⁻¹ ∈ P ∧
        orderOf ((g : G) * l * (g : G)⁻¹) = 2 ∧
        (g : G) * l * (g : G)⁻¹ ∉ K.map N.subtype := by
  intro N K W V P l hl hl2 hlW
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, S, hS⟩ := d.normalizer_fixed_sylow_local_position h hN hproper Q v hv hfix
  let lV : V := ⟨l, hl⟩
  have hlV2 : orderOf lV = 2 := (Subgroup.orderOf_coe lV).symm.trans hl2
  have hp : IsPGroup 2 (zpowers lV) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hlV2]; rfl)
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq V R S
  have hgm : g * lV * g⁻¹ ∈ (S : Subgroup V) := by
    rw [← hg]
    change g * lV * g⁻¹ ∈ (R : Subgroup V).map (MulAut.conj g).toMonoidHom
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hR (mem_zpowers lV))
  have hP : (g : G) * l * (g : G)⁻¹ ∈ P := by
    change (S : Subgroup V).map V.subtype = P at hS
    rw [← hS]
    exact mem_map_of_mem V.subtype hgm
  have hCX : K.map N.subtype ⊓ centralizer ({v} : Set G) = W :=
    d.normalizer_core_fixed_involution_centralizer h hN hproper Q v hv hfix
  have hlX : l ∉ K.map N.subtype := fun hx => hlW (hCX ▸ ⟨hx, hl.2⟩)
  have hgN : (g : G) ∈ normalizer (K.map N.subtype : Set G) := by
    apply le_normalizer_map N.subtype
    exact mem_map_of_mem N.subtype
      ((show normalizer (K : Set N) = ⊤ from normalizer_eq_top K).symm ▸
        (show (⟨g, g.property.1⟩ : N) ∈ (⊤ : Subgroup N) from mem_top _))
  refine ⟨g, hP, ((MulAut.conj (g : G)).orderOf_eq l).trans hl2, ?_⟩
  exact fun hm => hlX ((mem_normalizer_iff.mp hgN l).mpr hm)



/-- Every involution in the supplied Sylow outside the original core belongs
to the normalizer omega subgroup. -/
public theorem sylow_outer_involution_mem_normalizer_omega
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    ∀ y : G, y ∈ (d.sylow : Subgroup G) → orderOf y = 2 →
      y ∉ J.map H.subtype → y ∈ W := by
  intro H J N K W y hy hy2 hyJ
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let U := omega₁ K (p := 2)
  let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
  let yH : H := ⟨y, d.sylow_le_centralizer hy⟩
  have hyH2 : orderOf yH = 2 := (Subgroup.orderOf_coe yH).symm.trans hy2
  have hyHJ : yH ∉ J := fun hh => hyJ (mem_map_of_mem H.subtype hh)
  have hfixed : Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) = 8 := by
    have hh := parrott_outer_involution_fixed_card z h yH hyH2 hyHJ
    rw [← card_map_of_injective E.subtype_injective, subgroupOf_map_subtype] at hh
    change Nat.card (centralizer ({y} : Set G) ⊓ E : Subgroup G) = 8 at hh
    rw [inf_comm] at hh
    exact hh
  have hZU : Nat.card ZU = 8 :=
    (card_map_of_injective ((N.subtype_injective.comp K.subtype_injective).comp
      U.subtype_injective)).trans (d.normalizer_core_omega_structure h hN hproper).2.1
  have heq : E ⊓ centralizer ({y} : Set G) = ZU :=
    eq_of_le_of_card_ge (d.sylow_outer_derived_fixed_le_omega_center h hN hproper y hy hyJ)
      (by rw [hfixed, hZU])
  have hW : N ⊓ centralizer (ZU : Set G) = W :=
    d.normalizer_omega_center_centralizer h hN hproper
  rw [← hW]
  refine ⟨d.sylow_le_normalizer hy, ?_⟩
  intro u hu
  exact mem_centralizer_singleton_iff.mp ((heq.symm ▸ hu).2)

/-- Every involution of V outside W has a conjugate in the original core
outside its derived subgroup; the conjugator lies in V itself. -/
public theorem normalizer_fixed_outside_omega_transport
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let V := N ⊓ centralizer ({v} : Set G)
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ l : G, l ∈ V → orderOf l = 2 → l ∉ W →
      ∃ g : V, (g : G) * l * (g : G)⁻¹ ∈ J.map H.subtype ∧
        (g : G) * l * (g : G)⁻¹ ∉ E := by
  intro N K W V H J E l hl hl2 hlW
  obtain ⟨g, hgP, hg2, hgX⟩ :=
    d.normalizer_fixed_outside_omega_conjugate_into_sylow h hN hproper Q v hv hfix l hl hl2 hlW
  have hWX : W ≤ K.map N.subtype := by
    rintro x ⟨k, hk, rfl⟩
    exact mem_map_of_mem N.subtype k.property
  have hgW : (g : G) * l * (g : G)⁻¹ ∉ W := fun hh => hgX (hWX hh)
  refine ⟨g, ?_, ?_⟩
  · by_contra hout
    exact hgW (d.sylow_outer_involution_mem_normalizer_omega h hN hproper _ hgP.1 hg2 hout)
  · exact fun hh => hgW ((le_sup_left.trans
      (d.elementary_join_le_normalizer_core_omega h hN hproper)) hh)



/-- An outside-omega involution in P supplies an original-core fixed join
inside V, H-conjugate to the supplied F and with proper Sylow normalizer. -/
public theorem normalizer_fixed_outside_omega_fixed_join
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let V := N ⊓ centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ w : G, w ∈ P → orderOf w = 2 → w ∉ W →
      ∃ e : ParrottSecondElementaryData z, (e.a : G) = w ∧
        (∃ a : H, d.F.map (MulAut.conj (a : G)).toMonoidHom = e.F) ∧
        e.F ≤ V ∧ v ∈ E ⊓ e.F ∧
        (e.sylow : Subgroup G) < normalizer (e.F : Set G) := by
  intro N K W V P H J E w hw hw2 hwW
  have hwJ : w ∈ J.map H.subtype := by
    by_contra hout
    exact hwW (d.sylow_outer_involution_mem_normalizer_omega h hN hproper w hw.1 hw2 hout)
  have hwE : w ∉ E := fun hh => hwW ((le_sup_left.trans
    (d.elementary_join_le_normalizer_core_omega h hN hproper)) hh)
  obtain ⟨wH, hwHJ, heq⟩ := hwJ
  have hwHD : wH ∉ (commutator J).map J.subtype := by
    intro hh
    have hm := mem_map_of_mem H.subtype hh
    rw [map_map] at hm
    exact hwE (heq ▸ hm)
  obtain ⟨e, hea⟩ := parrott_second_elementary_of_core_involution z h wH hwHJ
    ((Subgroup.orderOf_coe wH).symm.trans ((congrArg orderOf heq).trans hw2)) hwHD
  have hew : (e.a : G) = w := (congrArg H.subtype hea).trans heq
  obtain ⟨a, ha⟩ := d.exists_conjugate_fixed_join e h
  have hvE : v ∈ E :=
    (d.normalizer_core_omega_structure h hN hproper).2.2.1
      (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).1 |>.1
  have hve : v ∈ e.F := by
    rw [e.fixed_join]
    apply mem_sup_right
    refine ⟨hvE, ?_⟩
    rw [hew]
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hw.2).symm
  have heV : e.F ≤ V := by
    let : IsElementaryAbelian 2 e.F := e.elementary
    intro x hx
    exact ⟨d.sylow_le_normalizer (d.core_le_sylow (e.le_core hx)),
      mem_centralizer_singleton_iff.mpr (setLike_mul_comm hx hve)⟩
  have heproper : (e.sylow : Subgroup G) < normalizer (e.F : Set G) := by
    apply lt_of_le_of_ne e.sylow_le_normalizer
    intro he
    exact hproper.ne (e.normalizer_eq_sylow_of_normalizer_eq_sylow d h he.symm).symm
  exact ⟨e, hew, ⟨a, ha⟩, heV, ⟨hvE, hve⟩, heproper⟩

/-- The fixed join has no extra normalizer in C_G(v) once v is outside
its own normalizer omega center. -/
public theorem fixed_join_normalizer_le_of_outside_omega_center
    (d e : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (heproper : (e.sylow : Subgroup G) < normalizer (e.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let M := normalizer (e.F : Set G)
    let K := pCore 2 M
    let U := omega₁ K (p := 2)
    let ZU := (center U).map ((M.subtype.comp K.subtype).comp U.subtype)
    ∀ v : G, v ∈ E ⊓ e.F → v ∉ ZU →
      centralizer ({v} : Set G) ⊓ normalizer (e.F : Set G) ≤
        normalizer (d.F : Set G) ⊓ centralizer ({v} : Set G) := by
  intro H J E M K U ZU v hv hvZU
  rw [inf_comm, e.normalizer_elementary_outside_omega_center_centralizer h hN heproper v hv hvZU]
  exact inf_le_inf_right _ (d.core_le_sylow.trans d.sylow_le_normalizer)

end Stellmacher.Recognition.ParrottSecondElementaryData
