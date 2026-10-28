module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadFixedStructure
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Ambient
public import Mathlib.GroupTheory.Complement
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups.NativePlaneFlags

/-!
# The split source hexad quotient

Write H = C_G(z), Q = O₂(H), L = G₁,₃ and N = L ∩ N_H(X).
The original Frattini product gives L = QN and N ∩ Q = Z(H).
For the constructed elementary subgroup E, its intersection with N is
the rank-five factor P = O₂(L) ∩ C_H(X). These equalities show that the
images of Q and N in the literal quotient L/E are complementary. The
Q-image is elementary of order 64 and the N-image has order 2160.

The native six-letter action descends through E and restricts to a
surjection of the complement onto S₆. Its kernel is exactly the image
of the original cubic Sylow subgroup and has order three. Thus no
cubic factor is discarded when passing to the source quotient.

Source: Aschbacher–Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.6)(2), p.598, DOI 10.1007/BF01232280.
This proves the splitting and marked cubic-cover clauses; the isomorphism
type of the cover and E = J(T) remain separate source assertions.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Sporadic.Mathieu LocalGeometry
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e))

/-- The original cubic normalizer inside the full hexad preimage. -/
def originalHexadNormalizer (B : Finset (Fin 22)) : Subgroup (centralizer z) :=
  originalPlaneHexad e B ⊓ fullCubicNormalizer e X

include h in
/-- Restrict the original Frattini product to the full hexad preimage. -/
theorem originalPlaneHexad_product (B : Finset (Fin 22)) :
    core z ⊔ originalHexadNormalizer e X B = originalPlaneHexad e B := by
  have hQ : core z ≤ originalPlaneHexad e B :=
    (CubicLift.core_le e).trans (originalPlaneHexad_cubic_le e B)
  apply le_antisymm (sup_le hQ inf_le_left)
  intro g hg
  obtain ⟨q,n,he⟩ := exists_core_mul_cubicNormalizer e h X g
  have hn : n.val ∈ originalPlaneHexad e B := by
    have hh := (originalPlaneHexad e B).mul_mem
      ((originalPlaneHexad e B).inv_mem (hQ q.property)) hg
    rw [←he] at hh
    simpa only [inv_mul_cancel_left] using hh
  rw [←he]
  exact mul_mem_sup q.property ⟨hn,n.property⟩

/-- The constructed E lies in the source overlap. -/
theorem originalHexadElementary_le (B : Finset (Fin 22)) :
    originalHexadElementary h e X B ≤ originalPlaneHexad e B := by
  apply le_trans _ (pCoreIn_le 2 _)
  rw [originalPlaneHexad_twoCore h e X B]
  exact sup_le_sup (originalHexadFixedCore_le h e X B) le_rfl

/-- Normality is relative to the source overlap. -/
theorem originalHexadElementary_normal {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ((originalHexadElementary h e X B).subgroupOf (originalPlaneHexad e B)).Normal :=
  normal_subgroupOf_of_le_normalizer (originalHexadElementary_data h e X hB).2.2.2.2.1

include h in
/-- The normalizer meets Q in the original central involution subgroup. -/
theorem originalHexadNormalizer_inf_core (B : Finset (Fin 22)) :
    originalHexadNormalizer e X B ⊓ core z = center (centralizer z) := by
  apply le_antisymm
  · exact (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans
      (fullCubicNormalizer_core_intersection h e X).le
  · refine le_inf (le_inf ?_ (center_le_normalizer _)) ?_
    · have hc : center (centralizer z) ≤ core z := by
        rw [←core_center_eq_centralizer_center h]
        exact map_subtype_le _
      exact hc.trans ((CubicLift.core_le e).trans (originalPlaneHexad_cubic_le e B))
    · rw [←core_center_eq_centralizer_center h]
      exact map_subtype_le _

/-- The normalizer meets E in exactly the rank-five source factor. -/
theorem originalHexadElementary_inf_normalizer {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    originalHexadElementary h e X B ⊓ originalHexadNormalizer e X B =
      originalHexadCore h e X B := by
  have hPC : originalHexadCore h e X B ≤ fullCubicCentralizer e X :=
    (originalHexadCore_eq_source h e X B).le.trans inf_le_right
  have hPN : originalHexadCore h e X B ≤ originalHexadNormalizer e X B :=
    le_inf (le_sup_right.trans (originalHexadElementary_le h e X B))
      (hPC.trans (Subgroup.centralizer_le_normalizer _))
  apply le_antisymm _ (le_inf le_sup_right hPN)
  intro g hg
  have hr : g ∈ core z ⊔ originalHexadCore h e X B :=
    (sup_le_sup (originalHexadFixedCore_le h e X B) le_rfl) hg.1
  obtain ⟨q,hq,p,hp,he⟩ := mem_sup_of_normal_left.mp hr
  have hqN : q ∈ originalHexadNormalizer e X B := by
    have hh := (originalHexadNormalizer e X B).mul_mem hg.2
      ((originalHexadNormalizer e X B).inv_mem (hPN hp))
    rw [←he,mul_inv_cancel_right] at hh
    exact hh
  have hz := (originalHexadNormalizer_inf_core h e X B).le ⟨hqN,hq⟩
  rw [←he]
  exact mul_mem ((originalHexadCore_data h e X hB).2.2 hz) hp

private theorem quotient_split {A J : Type*} [Group A] [Group J]
    (Q U P N : Subgroup A) [Q.Normal]
    (f : A →* J) (hf : Function.Surjective f)
    (hk : f.ker = U ⊔ P) (hUQ : U ≤ Q) (hPN : P ≤ N)
    (hn : P ≤ normalizer (U : Set A))
    (hi : Q ⊓ N ≤ U) (hgen : Q ⊔ N = ⊤) :
    (Q.map f).IsComplement' (N.map f) := by
  have hd : Disjoint (Q.map f) (N.map f) := by
    apply disjoint_def.mpr
    rintro _ ⟨q,hq,rfl⟩ ⟨n,hnN,he⟩
    have hqn : q*n⁻¹ ∈ U ⊔ P := by
      rw [←hk]
      change f (q*n⁻¹)=1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hprod : q*n⁻¹ ∈ (U : Set A)*(P : Set A) := by
      rw [←coe_mul_of_right_le_normalizer_left U P hn]
      exact hqn
    obtain ⟨u,hu,p,hp,hup⟩ := hprod
    have heq : u⁻¹*q=p*n := by
      have hqp : q=u*p*n := (mul_inv_eq_iff_eq_mul.mp hup.symm)
      rw [hqp]
      group
    have hqN : u⁻¹*q ∈ N := heq ▸ N.mul_mem (hPN hp) hnN
    have hqU : q ∈ U := by
      have hx := hi ⟨Q.mul_mem (Q.inv_mem (hUQ hu)) hq,hqN⟩
      simpa only [mul_inv_cancel_left] using U.mul_mem hu hx
    exact show f q=1 from (show q ∈ f.ker from hk.symm ▸ (le_sup_left : U ≤ U ⊔ P) hqU)
  refine ⟨mul_injective_of_disjoint hd,?_⟩
  intro j
  obtain ⟨a,rfl⟩ := hf j
  obtain ⟨q,hq,n,hn,hqn⟩ := mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top a)
  exact ⟨(⟨f q,mem_map_of_mem f hq⟩,⟨f n,mem_map_of_mem f hn⟩),by
    change f q*f n=f a
    rw [←map_mul,hqn]⟩

/-- The literal quotient images are complementary, establishing the splitting. -/
theorem originalHexadQuotient_split {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    let := originalHexadElementary_normal h e X hB
    let L := originalPlaneHexad e B
    let f := QuotientGroup.mk' ((originalHexadElementary h e X B).subgroupOf L)
    (((core z).subgroupOf L).map f).IsComplement'
      (((originalHexadNormalizer e X B).subgroupOf L).map f) := by
  let := originalHexadElementary_normal h e X hB
  let L := originalPlaneHexad e B
  let U := originalHexadFixedCore h e X B
  let P := originalHexadCore h e X B
  let N := originalHexadNormalizer e X B
  have hQ : core z ≤ L := (CubicLift.core_le e).trans (originalPlaneHexad_cubic_le e B)
  have hU : U ≤ L := (originalHexadFixedCore_le h e X B).trans hQ
  have hP : P ≤ L := le_sup_right.trans (originalHexadElementary_le h e X B)
  have hPC : P ≤ fullCubicCentralizer e X :=
    (originalHexadCore_eq_source h e X B).le.trans inf_le_right
  apply quotient_split ((core z).subgroupOf L) (U.subgroupOf L) (P.subgroupOf L)
    (N.subgroupOf L) _ (QuotientGroup.mk'_surjective _)
  · rw [QuotientGroup.ker_mk',←subgroupOf_sup hU hP]
    rfl
  · exact comap_mono (originalHexadFixedCore_le h e X B)
  · exact comap_mono (le_inf hP (hPC.trans (Subgroup.centralizer_le_normalizer _)))
  · intro p hp
    apply mem_normalizer_iff.mpr
    intro u
    change (u.val ∈ U ↔ p.val*u.val*p.val⁻¹ ∈ U)
    have hc := (le_centralizer_iff.mp (originalHexadFixedCore_centralizes h e X B)) hp
    exact mem_normalizer_iff.mp (Subgroup.centralizer_le_normalizer _ hc) u.val
  · intro u hu
    exact center_le_originalHexadFixedCore h e X B
      ((originalHexadNormalizer_inf_core h e X B).le ⟨hu.2,hu.1⟩)
  · rw [←subgroupOf_sup hQ (show N ≤ L from inf_le_left),
      originalPlaneHexad_product h e X B,subgroupOf_self]

open LocalGeometry.LocalSubgroups

include h in
theorem originalPlaneHexad_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card (originalPlaneHexad e B)=283115520 := by
  let f := CubicLift.projection e
  have hk : f.ker ≤ originalPlaneHexad e B := originalPlaneHexad_cubic_le e B
  have him : (originalPlaneHexad e B).map f=designStabilizer B :=
    map_comap_eq_self_of_surjective (CubicLift.projection_surjective e) _
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map (originalPlaneHexad e B) f
  rw [inf_eq_right.mpr hk,him,native_design_hex_card hB] at hc
  have hkc : Nat.card f.ker=3*2^13 := CubicLift.subgroup_card e h
  rw [hkc] at hc
  exact hc.symm

/-- The Q-image is elementary of rank six in the literal quotient. -/
theorem originalHexadQuotient_core_data {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    letI := originalHexadElementary_normal h e X hB
    let L := originalPlaneHexad e B
    let f := QuotientGroup.mk' ((originalHexadElementary h e X B).subgroupOf L)
    IsElementaryAbelian 2 (((core z).subgroupOf L).map f) ∧
      Nat.card (((core z).subgroupOf L).map f)=64 := by
  let := originalHexadElementary_normal h e X hB
  let L := originalPlaneHexad e B
  let E := originalHexadElementary h e X B
  let U := originalHexadFixedCore h e X B
  let f := QuotientGroup.mk' (E.subgroupOf L)
  have hQ : core z ≤ L := (CubicLift.core_le e).trans (originalPlaneHexad_cubic_le e B)
  have hU : U ≤ L := (originalHexadFixedCore_le h e X B).trans hQ
  obtain ⟨hUel,hUc,hEel,hEc,hEn,hEQ⟩ := originalHexadElementary_data h e X hB
  have hi : (core z).subgroupOf L ⊓ f.ker = U.subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    change (core z ⊓ E).subgroupOf L = U.subgroupOf L
    rw [inf_comm,hEQ]
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map ((core z).subgroupOf L) f
  rw [hi,Nat.card_congr (subgroupOfEquivOfLe hU).toEquiv,hUc,
    Nat.card_congr (subgroupOfEquivOfLe hQ).toEquiv,h.core_card] at hc
  have hs (x : ((core z).subgroupOf L).map f) : x^2=1 := by
    obtain ⟨q,hq,he⟩ := x.property
    apply Subtype.ext
    change x.val^2=1
    rw [←he,←map_pow]
    apply (QuotientGroup.eq_one_iff (q^2)).mpr
    let q0 : core z := ⟨q.val,hq⟩
    let := h.extraspecial
    let := IsExtraspecial.quotient_elementary_abelian 2 (core z)
    have hq2 : q0^2 ∈ center (core z) := (QuotientGroup.eq_one_iff _).mp
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (core z ⧸ center (core z)))
        (QuotientGroup.mk' (center (core z)) q0))
    have hz : (q0^2 : core z).val ∈ center (centralizer z) := by
      rw [←core_center_eq_centralizer_center h]
      exact mem_map_of_mem _ hq2
    exact (le_sup_left : U ≤ E) (center_le_originalHexadFixedCore h e X B hz)
  have hc0 : Nat.card (((core z).subgroupOf L).map f)=64 := by omega
  refine ⟨?_,hc0⟩
  have hi (x : ((core z).subgroupOf L).map f) : x⁻¹=x :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs x)
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  intro a b
  rw [←hi (a*b),mul_inv_rev,hi,hi]

theorem originalHexadQuotient_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    letI := originalHexadElementary_normal h e X hB
    Nat.card (originalPlaneHexad e B ⧸
      (originalHexadElementary h e X B).subgroupOf (originalPlaneHexad e B))=138240 := by
  let := originalHexadElementary_normal h e X hB
  have hc := ((originalHexadElementary h e X B).subgroupOf
    (originalPlaneHexad e B)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (originalHexadElementary_le h e X B)).toEquiv,
    (originalHexadElementary_data h e X hB).2.2.2.1,originalPlaneHexad_card h e hB] at hc
  change ((originalHexadElementary h e X B).subgroupOf (originalPlaneHexad e B)).index=138240
  omega

theorem originalHexadQuotient_normalizer_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    letI := originalHexadElementary_normal h e X hB
    let L := originalPlaneHexad e B
    let f := QuotientGroup.mk' ((originalHexadElementary h e X B).subgroupOf L)
    Nat.card (((originalHexadNormalizer e X B).subgroupOf L).map f)=2160 := by
  let := originalHexadElementary_normal h e X hB
  have hc := (originalHexadQuotient_split h e X hB).card_mul_card
  rw [(originalHexadQuotient_core_data h e X hB).2,originalHexadQuotient_card h e X hB] at hc
  omega

/-- The literal permutation action on the native hexad. -/
def originalHexadSymmetricProjection {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    originalPlaneHexad e B →* Equiv.Perm (Fin 6) :=
  (nativePlaneAction hB).comp ((CubicLift.projection e).subgroupComap (designStabilizer B))

theorem originalHexadSymmetricProjection_surjective {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) : Function.Surjective (originalHexadSymmetricProjection e hB) :=
  (native_plane_action_surjective hB).comp
    ((CubicLift.projection e).subgroupComap_surjective_of_surjective _
      (CubicLift.projection_surjective e))

theorem originalHexadSymmetricProjection_core {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) : (core z).subgroupOf (originalPlaneHexad e B) ≤
      (originalHexadSymmetricProjection e hB).ker := by
  intro q hq
  change nativePlaneAction hB _ = 1
  have he : (CubicLift.projection e).subgroupComap (designStabilizer B) q = 1 := by
    apply Subtype.ext
    exact CubicLift.core_le e hq
  exact (congrArg (nativePlaneAction hB) he).trans (map_one _)

theorem originalHexadSymmetricProjection_elementary {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) :
    (originalHexadElementary h e X B).subgroupOf (originalPlaneHexad e B) ≤
      (originalHexadSymmetricProjection e hB).ker := by
  let E := (originalHexadElementary h e X B).subgroupOf (originalPlaneHexad e B)
  let f := originalHexadSymmetricProjection e hB
  let := originalHexadElementary_normal h e X hB
  let := (originalHexadElementary_data h e X hB).2.2.1
  have hp : IsPGroup 2 (E.map f) :=
    ((IsElementaryAbelian.isPGroup 2 (originalHexadElementary h e X B)).comap_subtype).map f
  let : (E.map f).Normal := Normal.map inferInstance f
    (originalHexadSymmetricProjection_surjective e hB)
  have he : E.map f ≤ pCore 2 (Equiv.Perm (Fin 6)) := le_sSup ⟨inferInstance,hp⟩
  rw [Theory.SpecificGroups.SymmetricSix.s6_twoCore_eq_bot] at he
  intro x hx
  exact he (mem_map_of_mem f hx)

/-- The same hexad action descended through the constructed E. -/
def originalHexadQuotientProjection {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    letI := originalHexadElementary_normal h e X hB
    (originalPlaneHexad e B ⧸ (originalHexadElementary h e X B).subgroupOf
      (originalPlaneHexad e B)) →* Equiv.Perm (Fin 6) := by
  let := originalHexadElementary_normal h e X hB
  exact QuotientGroup.lift _ (originalHexadSymmetricProjection e hB)
    (originalHexadSymmetricProjection_elementary h e X hB)

theorem originalHexadQuotientProjection_apply {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (x : originalPlaneHexad e B) :
    letI := originalHexadElementary_normal h e X hB
    originalHexadQuotientProjection h e X hB
      (QuotientGroup.mk' ((originalHexadElementary h e X B).subgroupOf
        (originalPlaneHexad e B)) x) = originalHexadSymmetricProjection e hB x := rfl

/-- Restrict the descended native action to the actual normalizer image. -/
def originalHexadComplementProjection {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    letI := originalHexadElementary_normal h e X hB
    let L := originalPlaneHexad e B
    let q := QuotientGroup.mk' ((originalHexadElementary h e X B).subgroupOf L)
    (((originalHexadNormalizer e X B).subgroupOf L).map q) →* Equiv.Perm (Fin 6) := by
  let := originalHexadElementary_normal h e X hB
  exact (originalHexadQuotientProjection h e X hB).comp (_root_.Subgroup.subtype _)

theorem originalHexadComplementProjection_surjective {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) :
    Function.Surjective (originalHexadComplementProjection h e X hB) := by
  let := originalHexadElementary_normal h e X hB
  let L := originalPlaneHexad e B
  let q := QuotientGroup.mk' ((originalHexadElementary h e X B).subgroupOf L)
  let r := originalHexadQuotientProjection h e X hB
  intro s
  obtain ⟨l,hl⟩ := originalHexadSymmetricProjection_surjective e hB s
  obtain ⟨⟨a,b⟩,hab⟩ := (originalHexadQuotient_split h e X hB).2 (q l)
  have ha : r a = 1 := by
    obtain ⟨v,hv,hva⟩ := a.property
    rw [←hva]
    exact originalHexadSymmetricProjection_core e hB hv
  refine ⟨b,?_⟩
  change r b = s
  calc
    r b = r a * r b := by rw [ha,one_mul]
    _ = r (a.val*b.val) := (map_mul r _ _).symm
    _ = r (q l) := congrArg r hab
    _ = s := hl

theorem originalHexadComplementProjection_kernel_card {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) :
    Nat.card (originalHexadComplementProjection h e X hB).ker = 3 := by
  have hc := (originalHexadComplementProjection h e X hB).ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr
    (originalHexadComplementProjection_surjective h e X hB),card_top,
    Theory.SpecificGroups.SymmetricSix.s6_order,
    originalHexadQuotient_normalizer_card h e X hB] at hc
  omega

/-- The kernel of the complement's six-letter action is exactly the image
of the original cubic Sylow subgroup, through the same quotient map. -/
theorem originalHexadComplementProjection_kernel {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) :
    letI := originalHexadElementary_normal h e X hB
    let L := originalPlaneHexad e B
    let q := QuotientGroup.mk' ((originalHexadElementary h e X B).subgroupOf L)
    let N := ((originalHexadNormalizer e X B).subgroupOf L).map q
    (originalHexadComplementProjection h e X hB).ker.map N.subtype =
      ((cubicSylowImage e X).subgroupOf L).map q := by
  let := originalHexadElementary_normal h e X hB
  let L := originalPlaneHexad e B
  let E := (originalHexadElementary h e X B).subgroupOf L
  let q := QuotientGroup.mk' E
  let N := ((originalHexadNormalizer e X B).subgroupOf L).map q
  let C := (cubicSylowImage e X).subgroupOf L
  let f := originalHexadComplementProjection h e X hB
  have hCL : cubicSylowImage e X ≤ L :=
    (map_subtype_le _).trans (originalPlaneHexad_cubic_le e B)
  have hCN : C ≤ (originalHexadNormalizer e X B).subgroupOf L := by
    intro x hx
    exact ⟨x.property,le_normalizer hx⟩
  have hC : Nat.card C = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCL).toEquiv,
      cubicSylowImage,card_map_of_injective (CubicLift.subgroup e).subtype_injective,
      cubicSylow_card e h X]
  have hp : IsPGroup 3 C := (X.isPGroup'.map (CubicLift.subgroup e).subtype).comap_subtype
  let := (originalHexadElementary_data h e X hB).2.2.1
  have hd : Disjoint C E := hp.disjoint_of_coprime
    ((IsElementaryAbelian.isPGroup 2 (originalHexadElementary h e X B)).comap_subtype)
    (by decide)
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map C q
  rw [QuotientGroup.ker_mk',hd.eq_bot,Nat.card_unique,one_mul,hC] at hc
  have hle : C.map q ≤ f.ker.map N.subtype := by
    rintro _ ⟨x,hx,rfl⟩
    let n : N := ⟨q x,mem_map_of_mem q (hCN hx)⟩
    refine ⟨n,?_,rfl⟩
    change originalHexadSymmetricProjection e hB x=1
    have he : (CubicLift.projection e).subgroupComap (designStabilizer B) x = 1 := by
      apply Subtype.ext
      exact (map_subtype_le _ : cubicSylowImage e X ≤ CubicLift.subgroup e) hx
    exact (congrArg (nativePlaneAction hB) he).trans (map_one _)
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective N.subtype_injective,
    originalHexadComplementProjection_kernel_card h e X hB,hc]

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
