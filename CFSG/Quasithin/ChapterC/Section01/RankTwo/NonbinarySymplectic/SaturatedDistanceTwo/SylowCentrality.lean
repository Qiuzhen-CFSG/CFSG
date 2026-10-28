module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SylowLayers
public import Theory.SpecificGroups.SymplecticFour.Sylow.InvariantSubspaces
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.CommutatorRows
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Frattini
public import Theory.SpecificGroups.SymplecticFour.Sylow.SelfCentralizingElementary
public import Theory.Frattini.SquareImage
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The large Sylow-image contradiction in MS93 (3.7)(1)

Suppose an actual critical image has order q squared and the full radical
has Sylow image. At the opposite endpoint its quadratic action has a
natural fixed plane. The same full radical stabilizes that plane, so the
natural quotient has a fixed subspace of index q. Lifting fixed vectors
through the original cover and using Z = U Z_t identifies the fixed
subgroup in the original critical image: it has order q. This comparison
retains the whole covering kernel and the entire Z_t attachment.

A normal elementary subgroup of order q squared in the symplectic Sylow
group cannot have this fixed subgroup. Its product with the Sylow center
would be one elementary wing; the other wing then generates the quotient.
The equality of the Sylow Frattini subgroup and its center contradicts
the prescribed intersection. Thus both full-Sylow critical images have
order q. Together with the saturated parabolic alternatives, this proves
[Z′,T] ≤ Q at both endpoints with the original full cores as kernels.

The reversed triple commutators and later critical-pair selection still
require their separate source arguments before the field restriction.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(1), printed p.873.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Matrix Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def fixedModulo (S : Subgroup (Sp F)) (W : Submodule F (Vector F)) : Submodule F (Vector F) :=
  ⨅ g : S, W.comap (symplecticNatural 2 g.val - LinearMap.id)

omit [Finite F] [CharP F 2] in
private theorem mem_fixedModulo (S : Subgroup (Sp F)) (W : Submodule F (Vector F)) (v : Vector F) :
    v ∈ fixedModulo S W ↔ ∀ g ∈ S, g • v-v ∈ W := by
  simp only [fixedModulo,Submodule.mem_iInf,Submodule.mem_comap,
    LinearMap.sub_apply,LinearMap.id_apply,symplecticNatural_apply]
  exact ⟨fun h g hg => h ⟨g,hg⟩,fun h g => h g.val g.property⟩

private theorem fixedModulo_plane (v : Vector F) :
    v ∈ fixedModulo unipotent (plane F) ↔ v (.inr 0)=0 := by
  rw [mem_fixedModulo]
  constructor
  · intro hv
    have hh := hv (element (1:F) 0 0 0).val (element 1 0 0 0).property 1
    simpa [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,element_matrix,mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two] using hh
  · intro hv g hg
    obtain ⟨⟨b,u,w,a⟩,he⟩ := element_surjective (⟨g,hg⟩ : unipotent)
    have he' := congrArg Subtype.val he
    change (element b u w a).val = g at he'
    rw [←he']
    intro i
    fin_cases i <;> simp [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,element_matrix,mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two,hv]

private theorem fixedModulo_plane_index :
    Nat.card (Vector F ⧸ fixedModulo unipotent (plane F)) = Nat.card F := by
  let f : Vector F →ₗ[F] F := LinearMap.proj (.inr 0)
  have hf : Function.Surjective f := by
    intro a
    exact ⟨Pi.single (.inr 0) a,by simp [f]⟩
  have hk : f.ker = fixedModulo unipotent (plane F) := by
    ext v
    exact (fixedModulo_plane v).symm
  rw [←hk]
  exact Nat.card_congr (f.quotKerEquivOfSurjective hf).toEquiv

private def vectorEquiv (u : Sp F) : Vector F ≃ₗ[F] Vector F where
  toLinearMap := symplecticNatural 2 u
  invFun v := u⁻¹ • v
  left_inv v := inv_smul_smul u v
  right_inv v := smul_inv_smul u v

omit [Finite F] [CharP F 2] in
private theorem mem_conjugate_subspace (u : Sp F) (W : Submodule F (Vector F)) (v : Vector F) :
    u • v ∈ W.map (symplecticNatural 2 u) ↔ v ∈ W := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact (show w=v from (vectorEquiv u).injective he) ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

omit [Finite F] [CharP F 2] in
private theorem fixedModulo_conjugate (u : Sp F) (S : Subgroup (Sp F))
    (W : Submodule F (Vector F)) :
    fixedModulo (S.map (MulAut.conj u).toMonoidHom) (W.map (symplecticNatural 2 u)) =
      (fixedModulo S W).map (symplecticNatural 2 u) := by
  ext v
  obtain ⟨w,rfl⟩ := (vectorEquiv u).surjective v
  change u • w ∈ _ ↔ u • w ∈ _
  rw [mem_conjugate_subspace,mem_fixedModulo,mem_fixedModulo]
  constructor
  · intro hv s hs
    have hh := hv _ (mem_map_of_mem (MulAut.conj u).toMonoidHom hs)
    have he : (MulAut.conj u s) • (u • w)-u • w = u • (s • w-w) := by
      simp [MulAut.conj_apply,mul_smul,smul_sub]
    change (MulAut.conj u s) • (u • w)-u • w ∈ _ at hh
    rw [he] at hh
    exact (mem_conjugate_subspace u W _).mp hh
  · rintro hv _ ⟨s,hs,rfl⟩
    have he : (MulAut.conj u s) • (u • w)-u • w = u • (s • w-w) := by
      simp [MulAut.conj_apply,mul_smul,smul_sub]
    change (MulAut.conj u s) • (u • w)-u • w ∈ _
    rw [he]
    exact (mem_conjugate_subspace u W _).mpr (hv s hs)

private theorem fixedModulo_sylow_plane_index (S : Sylow 2 (Sp F))
    (W : Submodule F (Vector F)) (hdim : Module.finrank F W = 2)
    (hW : (S : Subgroup (Sp F)) ≤ Theory.SpecificGroups.SymplecticFour.stabilizer W) :
    Nat.card (Vector F ⧸ fixedModulo S W) = Nat.card F := by
  let := Fintype.ofFinite F
  obtain ⟨n,hn,hFn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2^(n:ℕ) := by simpa only [Nat.card_eq_fintype_card] using hFn
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF n.pos)
  have hSu : (S : Subgroup (Sp F)).map (MulAut.conj u).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hu
  have hWu : W.map (symplecticNatural 2 u) = plane F := by
    apply unipotent_invariant_plane_unique
    · rw [←hSu]
      rintro _ ⟨s,hs,rfl⟩
      rw [mem_stabilizer_iff]
      rintro _ ⟨v,hv,rfl⟩
      change (MulAut.conj u s) • (u • v) ∈ _
      have he : (MulAut.conj u s) • (u • v)=u • (s • v) := by
        simp [MulAut.conj_apply,mul_smul]
      rw [he,mem_conjugate_subspace]
      exact (mem_stabilizer_iff W s).mp (hW hs) v hv
    · exact ((vectorEquiv u).finrank_map_eq W).trans hdim
  have he := fixedModulo_conjugate u (S : Subgroup (Sp F)) W
  rw [hSu,hWu] at he
  have hd : Module.finrank F (fixedModulo unipotent (plane F)) =
      Module.finrank F (fixedModulo S W) := by
    rw [he]
    exact (vectorEquiv u).finrank_map_eq _
  have hdq : Module.finrank F (Vector F ⧸ fixedModulo S W) =
      Module.finrank F (Vector F ⧸ fixedModulo unipotent (plane F)) := by
    have h1 := (fixedModulo S W).finrank_quotient_add_finrank
    have h2 := (fixedModulo unipotent (plane F)).finrank_quotient_add_finrank
    omega
  rw [Module.natCard_eq_pow_finrank (K := F),hdq,←Module.natCard_eq_pow_finrank (K := F)]
  exact fixedModulo_plane_index


omit [CharP F 2] in
private theorem large_quadratic_fixed_plane (A : Subgroup (Sp F))
    (hquad : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hlarge : Nat.card F < Nat.card A) :
    Module.finrank F (TwoLocalCover.fixedSpace A)=2 ∧
      normalizer (A : Set (Sp F)) ≤
        Theory.SpecificGroups.SymplecticFour.stabilizer (TwoLocalCover.fixedSpace A) := by
  have hself := large_quadratic_displacement_self_orthogonal A hquad hlarge
  have he : TwoLocalCover.fixedSpace A=displacementSpace A :=
    (orthogonal_displacementSpace A).symm.trans hself
  have hd := LinearMap.BilinForm.finrank_orthogonal
    (W := displacementSpace A) TwoLocalCover.form_nondegenerate
  rw [hself] at hd
  have hV : Module.finrank F (Vector F)=4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
  have hle := (displacementSpace A).finrank_le
  rw [hV] at hd hle
  refine ⟨by rw [he]; omega,?_⟩
  intro u hu
  rw [mem_stabilizer_iff]
  intro v hv x hx
  have hx' : u⁻¹*x*u ∈ A := (mem_normalizer_iff''.mp hu x).mp hx
  have hh := congrArg (fun w : Vector F => u • w) (hv _ hx')
  simpa only [mul_smul,smul_inv_smul] using hh

section Image
variable {T B W₀ : Type*} [Group T] [Group B] [AddCommGroup W₀] [Module (ZMod 2) W₀]
  [Algebra (ZMod 2) F]

private theorem image_centralizer_index_of_natural_plane
    (σ : Representation (ZMod 2) T W₀) (β : T →* Sp F)
    (S : Sylow 2 (Sp F)) (hS : β.range = S)
    (p : W₀ →ₗ[ZMod 2] Vector F) (hp : Function.Surjective p)
    (hβ : ∀ t w, p (σ t w)=β t • p w)
    (j : Multiplicative W₀ →* B) (χ : T →* B)
    (hj : ∀ t w, j (Multiplicative.ofAdd (σ t w))=χ t*j (Multiplicative.ofAdd w)*(χ t)⁻¹)
    (N : Submodule F (Vector F)) (hdim : Module.finrank F N=2)
    (hN : (S : Subgroup (Sp F)) ≤ Theory.SpecificGroups.SymplecticFour.stabilizer N)
    (hker : ∀ w, j (Multiplicative.ofAdd w)=1 ↔ p w ∈ N) :
    (centralizer (χ.range : Set B)).relIndex j.range=Nat.card F := by
  let D := fixedModulo S N
  let f : W₀ →ₗ[ZMod 2] (Vector F ⧸ D) :=
    (D.mkQ.restrictScalars (ZMod 2)).comp p
  let fm := f.toAddMonoidHom.toMultiplicative
  have hf : Function.Surjective fm := by
    intro v
    obtain ⟨x,hx⟩ := (Submodule.mkQ_surjective D) v.toAdd
    obtain ⟨w,hw⟩ := hp x
    refine ⟨Multiplicative.ofAdd w,?_⟩
    apply Multiplicative.toAdd.injective
    change D.mkQ (p w)=v.toAdd
    rw [hw]
    exact hx
  have hk : (centralizer (χ.range : Set B)).comap j = fm.ker := by
    ext w
    change j w ∈ centralizer (χ.range : Set B) ↔ f w.toAdd=0
    rw [show f w.toAdd = D.mkQ (p w.toAdd) from rfl,
      Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,mem_fixedModulo]
    have hstep (t : T) : χ t*j w=j w*χ t ↔ β t • p w.toAdd-p w.toAdd ∈ N := by
      rw [←hβ,←map_sub,←hker]
      rw [ofAdd_sub,map_div,div_eq_mul_inv,mul_inv_eq_one,hj]
      change χ t*j w=j w*χ t ↔ χ t*j w*(χ t)⁻¹=j w
      exact ⟨fun hh => by rw [hh,mul_inv_cancel_right],
        fun hh => mul_inv_eq_iff_eq_mul.mp hh⟩
    constructor
    · intro hw g hg
      obtain ⟨t,rfl⟩ := hS.symm ▸ hg
      exact (hstep t).mp (hw (χ t) ⟨t,rfl⟩)
    · intro hw g hg
      obtain ⟨t,rfl⟩ := hg
      exact (hstep t).mpr (hw (β t) (hS ▸ (show β t ∈ β.range from ⟨t,rfl⟩)))
  rw [←index_comap,hk,index_ker,MonoidHom.range_eq_top.mpr hf,Nat.card_congr (Subgroup.topEquiv).toEquiv]
  exact fixedModulo_sylow_plane_index S N hdim hN

end Image

private theorem normal_elementary_square_fixed_ne_field {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (A : Subgroup (unipotent (F := F))) [A.Normal] [IsElementaryAbelian 2 A]
    (hA : Nat.card A=Nat.card F^2)
    (hfix : Nat.card (A ⊓ center (unipotent (F := F)) : Subgroup (unipotent (F := F)))=Nat.card F) : False := by
  have hq : 1<Nat.card F := by
    rw [hF]
    exact one_lt_pow₀ (by decide) (by omega)
  have hZ : Nat.card (center (unipotent (F := F)))=Nat.card F^2 := by
    rw [←Nat.card_congr (centerEquiv (F := F)).toEquiv,Nat.card_prod]
    change Nat.card F*Nat.card F=Nat.card F^2
    ring
  obtain ⟨i,hi⟩ := elementary_le_wing A
  have hZle : center (unipotent (F := F)) ≤ wing i := by
    cases i
    · exact center_le_wings.trans inf_le_left
    · exact center_le_wings.trans inf_le_right
  have hcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    A (center (unipotent (F := F))) le_normalizer_of_normal
  rw [hA,hZ,hfix] at hcard
  have hjoin : A ⊔ center (unipotent (F := F))=wing i := by
    apply eq_of_le_of_card_ge (sup_le hi hZle)
    rw [card_wing]
    nlinarith
  have hw : wing (F := F) i ⊔ wing (!i)=⊤ := by
    cases i
    · exact wings_generate
    · rw [sup_comm]; exact wings_generate
  have hgen : A ⊔ wing (!i)=⊤ := by
    apply frattini_nongenerating
    rw [frattini_eq_center hF hn]
    rw [sup_assoc,sup_comm (wing (!i)),←sup_assoc,hjoin,hw]
  let f := QuotientGroup.mk' A
  have hfW : (wing (!i)).map f=⊤ := by
    have hh := congrArg (fun B : Subgroup (unipotent (F := F)) => B.map f) hgen
    rw [Subgroup.map_sup,show A.map f=⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hs (x : unipotent (F := F)) : f x^2=1 := by
    obtain ⟨w,hw,he⟩ := (show f x ∈ (wing (!i)).map f from hfW ▸ mem_top _)
    rw [←he,←map_pow]
    let := wing_elementary (F := F) (!i)
    have hw2 : w^2=1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (wing (!i))) ⟨w,hw⟩)
    rw [hw2,map_one]
  have hZA : center (unipotent (F := F)) ≤ A := by
    have hh := Theory.GroupTheory.frattini_le_ker_of_square_image f hs
    rwa [QuotientGroup.ker_mk',frattini_eq_center hF hn] at hh
  rw [inf_eq_right.mpr hZA,hZ] at hfix
  nlinarith

private theorem sylow_normal_elementary_square_fixed_ne_field {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (S : Sylow 2 (Sp F)) (A : Subgroup (Sp F)) [IsElementaryAbelian 2 A]
    (hAS : A ≤ S) (hnorm : (S : Subgroup (Sp F)) ≤ normalizer (A : Set (Sp F)))
    (hA : Nat.card A=Nat.card F^2)
    (hfix : Nat.card (A ⊓ centralizer (S : Set (Sp F)) : Subgroup (Sp F))=Nat.card F) : False := by
  let A₀ := A.subgroupOf S
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer hnorm
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hAS
  let e : S ≃* unipotent (F := F) := Sylow.equiv S (unipotentSylow hF (by omega))
  let B := A₀.map e.toMonoidHom
  let : B.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map e.toMonoidHom
  have hB : Nat.card B=Nat.card F^2 := by
    rw [card_map_of_injective e.injective,Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv]
    exact hA
  have hcenter : (center S).map e.toMonoidHom=center (unipotent (F := F)) := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change x ∈ center S at hx
      change e x ∈ center (unipotent (F := F))
      rw [mem_center_iff] at hx ⊢
      intro y
      obtain ⟨z,rfl⟩ := e.surjective y
      rw [←map_mul,←map_mul,hx z]
    · intro y hy
      refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
      change e.symm y ∈ center S
      rw [mem_center_iff] at hy ⊢
      intro z
      apply e.injective
      rw [map_mul,map_mul,e.apply_symm_apply,hy]
  have hfixed : Nat.card (B ⊓ center (unipotent (F := F)) : Subgroup (unipotent (F := F)))=Nat.card F := by
    rw [←hcenter,←Subgroup.map_inf _ _ _ e.injective,card_map_of_injective e.injective]
    have heq : A₀ ⊓ center S=(A ⊓ centralizer (S : Set (Sp F))).subgroupOf S := by
      ext x
      constructor
      · rintro ⟨hx,hc⟩
        refine ⟨hx,?_⟩
        intro y hy
        exact congrArg Subtype.val ((mem_center_iff.mp hc) ⟨y,hy⟩)
      · rintro ⟨hx,hc⟩
        refine ⟨hx,mem_center_iff.mpr ?_⟩
        intro y
        exact Subtype.ext (hc y.val y.property)
    rw [heq,Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hAS)).toEquiv]
    exact hfix
  exact normal_elementary_square_fixed_ne_field hF hn B hB hfixed

section CoverFixed
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
variable {B W : Type*} [Group B] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] [Algebra (ZMod 2) F]
private theorem embedded_cover_fixed_iff
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* B) (hj : Function.Injective j)
    (A : Subgroup B) (δ : A →* L (K := F))
    (hδ : ∀ x w, j (Multiplicative.ofAdd (σ (δ x) w))=
      x.val*j (Multiplicative.ofAdd w)*x.val⁻¹) (w : W) :
    j (Multiplicative.ofAdd w) ∈ centralizer (A : Set B) ↔
      p w ∈ TwoLocalCover.fixedSpace (δ.range.map (commutator (Sp F)).subtype) := by
  constructor
  · intro hw x hx
    obtain ⟨y,hy,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    have hfix : σ (δ v) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hδ,hw v.val v.property,mul_inv_cancel_right]
    have hh := congrArg p hfix
    rw [p.isIntertwining] at hh
    exact hh
  · intro hw v hv
    have hfix : σ (δ ⟨v,hv⟩) w=w :=
      cover_fixed_of_projection_fixed p hp (δ ⟨v,hv⟩) w
        (hw _ ⟨δ ⟨v,hv⟩,⟨⟨v,hv⟩,rfl⟩,rfl⟩)
    have hh := hδ ⟨v,hv⟩ w
    rw [hfix] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
end CoverFixed

section CoverAction
open CFSG.Quasithin.ChapterB.QuasisimpleSource Representation.OneCohomology
variable {J D V W : Type*} [Group J] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) J V} {τ : Representation (ZMod 2) D W}
  {L : Subgroup J}
private theorem marked_cover_action (s : MovedSection ρ L)
    (e : ActionEquiv (s.action.comp L.subtype) τ) (x : L) (v : s.space.toSubmodule) :
    MovedSection.coverAction s e (e.groupEquiv x) v=s.space.toRepresentation x.val v := by
  change s.space.toRepresentation (e.groupEquiv.symm (e.groupEquiv x)).val v=_
  rw [e.groupEquiv.symm_apply_apply]
end CoverAction

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open DistanceTwoRecognition ChapterB.QuasisimpleSource
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
private theorem full_marking_surjective
    {J D T : Type*} [Group J] [Group D] [Group T]
    (C : Subgroup J) (L : Subgroup D) (hC : C=⊤) (hL : L=⊤)
    (e : C ≃* L) (κ : T →* J) (hκ : Function.Surjective κ) :
    Function.Surjective (L.subtype.comp (e.toMonoidHom.comp
      (κ.codRestrict C (fun x => hC ▸ mem_top (κ x))))) := by
  have hsub : Function.Surjective L.subtype := by
    intro x
    exact ⟨⟨x,hL ▸ mem_top x⟩,rfl⟩
  have hres : Function.Surjective (κ.codRestrict C (fun x => hC ▸ mem_top (κ x))) := by
    intro x
    obtain ⟨y,hy⟩ := hκ x.val
    exact ⟨y,Subtype.ext hy⟩
  exact hsub.comp (e.surjective.comp hres)

section InnerCover
variable {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
variable {ρ : Representation (ZMod 2) J W} {C : Subgroup J}

private structure InnerVertexCover (T : Subgroup M) (s : MovedSection ρ C)
    (n : ℕ) (a : Vertex T) where
  field : BinaryField
  degree : field.degree=n
  equiv : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := field.Carrier))
  cover : IsCover (MovedSection.coverProjection s equiv)
  embedding : Multiplicative s.space.toSubmodule →* FreeAmalgam T
  injective : Function.Injective embedding
  range_eq : embedding.range=U T a
  actor : stabilizer T a →* Representation.SymplecticFourOrthogonalCover.L (K := field.Carrier)
  onto : Function.Surjective ((commutator (Sp field.Carrier)).subtype.comp actor)
  kernel : ((commutator (Sp field.Carrier)).subtype.comp actor).ker.map
    (stabilizer T a).subtype=Q T a
  conjugation : ∀ x w,
    embedding (Multiplicative.ofAdd (MovedSection.coverAction s equiv (actor x) w))=
      x.val*embedding (Multiplicative.ofAdd w)*x.val⁻¹
end InnerCover

variable {H : Type*} [Group H] [Finite H]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem inner_vertex_actor
    (g : Geometry d.radical) (hb : 0<g.b d.radical) {a : Vertex d.radical}
    (ha : color d.radical a=false) :
    Nonempty (InnerVertexCover d.radical (replacementMovedSection h d) n a) := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d ha
  have hFc : Nat.card E.Carrier=2^n := by rw [E.card_eq,hE]
  have hCtop : replacementComponent d=⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g hb)
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q=⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let α := (commutator (Sp E.Carrier)).subtype.comp γ
  have hγker : γ.ker=κ.ker := by
    ext x
    change e.groupEquiv (κC x)=1 ↔ κ x=1
    rw [e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  have hαker : α.ker=κ.ker :=
    (MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective).trans hγker
  have hαQ : α.ker.map (stabilizer d.radical a).subtype=Q d.radical a := by
    rw [hαker,hκQ]
  have hcomm : commutator (Sp E.Carrier)=⊤ :=
    Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top (by
      rw [hFc]
      exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary))
  have hαonto : Function.Surjective α :=
    full_marking_surjective _ _ hCtop hcomm e.groupEquiv κ hκ
  refine ⟨⟨E,hE,e,he,j,hj,hjr,γ,hαonto,hαQ,?_⟩⟩
  intro x w
  exact (congrArg (fun y => j (Multiplicative.ofAdd y))
    (marked_cover_action s e (κC x) w)).trans (hconj x w)

private theorem edge_action_fixed_iff {a t : Vertex d.radical}
    (ha : color d.radical a=false) (c : EdgeMarking h d a t) (x : Q d.radical t) :
    c.action x=1 ↔ x.val ∈ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
  change x ∈ c.action.ker ↔ _
  rw [c.action_kernel]
  change x.val ∈ Q d.radical a ↔ _
  rw [←MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a ha]
  exact ⟨And.right,fun hx => ⟨c.edge_le x.property,hx⟩⟩

private theorem large_sylow_critical_image_fixed_index
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical=2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (S₀ : Sylow 2 (Sp F)) (hS₀ : (S₀ : Subgroup (Sp F))=c.action.range)
    (hlarge : (Q d.radical z).relIndex (Z d.radical a)=(2^n)^2) :
    (centralizer (c.action.range : Set (Sp F))).relIndex
      (((Z d.radical z).subgroupOf (Q d.radical t)).map c.action)=2^n := by
  let := replacementComponent_normal h d
  let := finite_stabilizer d.radical z
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,γ,hαonto,hαQ,hinner⟩⟩ :=
    inner_vertex_actor h d g (by omega) path.end_color
  have hFc : Nat.card E.Carrier=2^n := by rw [E.card_eq,hE]
  let α := (commutator (Sp E.Carrier)).subtype.comp γ
  have hZaT : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a (g.exists_critical a path.start_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hat),
      g.distance_constant a path.start_color]
    change 1<g.b d.radical
    omega
  have hZzT : Z d.radical z ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1<g.b d.radical
    omega
  have hZaS := hZaT.trans c'.edge_le
  have hUzT : U d.radical z ≤ Q d.radical t := (U_le_Z z).trans hZzT
  let δ := γ.comp (inclusion hZaS)
  let β := α.comp (inclusion c'.edge_le)
  let A := (α.comp (inclusion hZaS)).range
  have hδ (x : Z d.radical a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (δ x) w))=
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    exact hinner (inclusion hZaS x) w
  have hquad := Sp4Four.SourceComparison.critical_embedded_natural_actor_quadratic
    path (by omega) (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he
    j hj hjr δ hδ
  have hquadA : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ v
    exact hquad (δ x) ⟨x,rfl⟩ (δ y) ⟨y,rfl⟩ v
  have hcardA : Nat.card A=Nat.card E.Carrier^2 :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZaS α hαQ).trans
      (hlarge.trans (by rw [hFc]))
  obtain ⟨hdim,hNnorm⟩ := large_quadratic_fixed_plane A hquadA (by
    rw [hcardA]
    have hq : 1<Nat.card E.Carrier := by
      rw [hFc]
      exact one_lt_pow₀ (by decide) (by have := h.nonbinary; omega)
    nlinarith)
  obtain ⟨P,hP⟩ := c'.exists_edge_sylow S₀
    (hS₀.trans (c.action_range.trans c'.action_range.symm))
  let S := P.mapSurjective (f := α) hαonto
  have hS : β.range=(S : Subgroup (Sp E.Carrier)) := by
    rw [MonoidHom.range_comp,inclusion_range]
    change _=(P : Subgroup (stabilizer d.radical z)).map α
    rw [hP]
  have hnorm : (S : Subgroup (Sp E.Carrier)) ≤ normalizer (A : Set (Sp E.Carrier)) := by
    let A₀ := (Z d.radical a).subgroupOf (stabilizer d.radical z)
    let T₀ := (Q d.radical t).subgroupOf (stabilizer d.radical z)
    have hn : T₀ ≤ normalizer (A₀ : Set (stabilizer d.radical z)) :=
      (comap_mono (c.edge_le.trans (Z_normalized d.radical a))).trans
        (le_normalizer_comap (stabilizer d.radical z).subtype)
    have hh := (map_mono (f := α) hn).trans (le_normalizer_map α)
    have hAr : A=A₀.map α := by
      change (α.comp (inclusion hZaS)).range=A₀.map α
      rw [MonoidHom.range_comp,inclusion_range]
    rw [←hS,MonoidHom.range_comp,inclusion_range,hAr]
    exact hh
  let p := MovedSection.coverProjection s e
  let σ := (MovedSection.coverAction s e).comp (γ.comp (inclusion c'.edge_le))
  let jT := j.codRestrict (Q d.radical t)
    (fun w => hUzT (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  let η := c.action.comp jT
  have hη (x : Q d.radical t) (w : s.space.toSubmodule) :
      η (Multiplicative.ofAdd (σ x w))=
        c.action x*η (Multiplicative.ofAdd w)*(c.action x)⁻¹ := by
    have hh : jT (Multiplicative.ofAdd (σ x w))=
        x*jT (Multiplicative.ofAdd w)*x⁻¹ := by
      apply Subtype.ext
      exact hinner (inclusion c'.edge_le x) w
    change c.action (jT (Multiplicative.ofAdd (σ x w)))=_
    rw [hh,map_mul,map_mul,map_inv]
    rfl
  have hηker (w : s.space.toSubmodule) :
      η (Multiplicative.ofAdd w)=1 ↔ p w ∈ TwoLocalCover.fixedSpace A := by
    have hk := edge_action_fixed_iff h d path.start_color c (jT (Multiplicative.ofAdd w))
    have hAeq : A=δ.range.map (commutator (Sp E.Carrier)).subtype := by
      change ((commutator (Sp E.Carrier)).subtype.comp δ).range=_
      exact MonoidHom.range_comp _ _
    rw [hAeq]
    have hh := embedded_cover_fixed_iff (MovedSection.coverAction s e) p he j hj
      (Z d.radical a) δ hδ w
    exact hk.trans hh
  have hi := image_centralizer_index_of_natural_plane σ β S hS p.toLinearMap he.1
    (fun x w => LinearMap.congr_fun (p.isIntertwining' (γ (inclusion c'.edge_le x))) w)
    η c.action hη (TwoLocalCover.fixedSpace A) hdim (hnorm.trans hNnorm) hηker
  have hjTr : jT.range=(U d.radical z).subgroupOf (Q d.radical t) := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      exact hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)
    · intro hx
      obtain ⟨w,hw⟩ := (show x.val ∈ j.range from hjr.symm ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
  have hZtZ := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
  have hZaQ := (g.omega_bound a path.start_color (by
    rw [g.distance_constant a path.start_color]
    change 0<g.b d.radical
    omega)).trans (omegaCenter_le _)
  have hZtQa := hZtZ.trans hZaQ
  have hZtT := hZtQa.trans c.core_le_edge
  have hηr : η.range=((Z d.radical z).subgroupOf (Q d.radical t)).map c.action := by
    rw [Z_eq_moving_sup_edge_of_sylow h d g hb path.end_color hzt c' S₀
      (hS₀.trans (c.action_range.trans c'.action_range.symm)),subgroupOf_sup hUzT hZtT,
      Subgroup.map_sup,show ((Z d.radical t).subgroupOf (Q d.radical t)).map c.action=⊥ from
        (Subgroup.map_eq_bot_iff _).mpr (by rw [c.action_kernel]; exact comap_mono hZtQa),sup_bot_eq]
    rw [MonoidHom.range_comp,hjTr]
  rw [hηr,hFc] at hi
  exact hi

/-- The fixed-centralizer count in the large-image Sylow branch of
MS93 (3.7)(1), computed using the opposite endpoint's actual natural cover. -/
theorem large_sylow_critical_image_fixed_card
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical=2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (S₀ : Sylow 2 (Sp F)) (hS₀ : (S₀ : Subgroup (Sp F))=c.action.range)
    (hlarge : (Q d.radical z).relIndex (Z d.radical a)=(2^n)^2) :
    Nat.card ((((Z d.radical z).subgroupOf (Q d.radical t)).map c.action) ⊓
      centralizer (c.action.range : Set (Sp F)) : Subgroup (Sp F))=2^n := by
  have hi := large_sylow_critical_image_fixed_index h d path hb hat hzt c c' S₀ hS₀ hlarge
  have hZzT : Z d.radical z ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1<g.b d.radical
    omega
  have hlarge' : (Q d.radical a).relIndex (Z d.radical z)=(2^n)^2 := by
    rcases paired_critical_indices_of_sylow h d path hb hat hzt c S₀ hS₀ with hs | hl
    · have hq : 1<2^n := one_lt_pow₀ (by decide) (by have := h.nonbinary; omega)
      have hh := hs.1
      rw [hlarge] at hh
      nlinarith only [hq,hh]
    · exact hl.2
  let B := ((Z d.radical z).subgroupOf (Q d.radical t)).map c.action
  have hBcard : Nat.card B=(2^n)^2 := by
    rw [←relIndex_ker,c.action_kernel,relIndex_subgroupOf hZzT,hlarge']
  have hh := relIndex_mul_relIndex (⊥ : Subgroup (Sp F))
    (B ⊓ centralizer (c.action.range : Set (Sp F))) B bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hi,hBcard] at hh
  have hq : 0<2^n := by positivity
  nlinarith only [hh,hq]


/-- Both actual critical images have order q when the common full radical
has Sylow image. The order-q conclusion is derived from the source geometry. -/
theorem critical_indices_eq_field_of_full_sylow
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical=2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (S₀ : Sylow 2 (Sp F)) (hS₀ : (S₀ : Subgroup (Sp F))=c.action.range) :
    (Q d.radical z).relIndex (Z d.radical a)=2^n ∧
      (Q d.radical a).relIndex (Z d.radical z)=2^n := by
  rcases paired_critical_indices_of_sylow h d path hb hat hzt c S₀ hS₀ with hs | hl
  · exact hs
  exfalso
  have hZzT : Z d.radical z ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1<g.b d.radical
    omega
  let A₀ := (Z d.radical z).subgroupOf (Q d.radical t)
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer
    (c'.edge_le.trans (Z_normalized d.radical z))
  let := g.Z_elementary (by omega : 0<g.b d.radical) z path.end_color
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hZzT
  let A := A₀.map c.action
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map c.action
  have hAS : A ≤ S₀ := (map_le_range _ _).trans_eq hS₀.symm
  have hn : (S₀ : Subgroup (Sp F)) ≤ normalizer (A : Set (Sp F)) := by
    rw [hS₀,MonoidHom.range_eq_map]
    exact (map_mono (show (⊤ : Subgroup (Q d.radical t)) ≤ normalizer (A₀ : Set (Q d.radical t)) from
      le_normalizer_of_normal)).trans (le_normalizer_map c.action)
  have hA : Nat.card A=Nat.card F^2 := by
    rw [←relIndex_ker,c.action_kernel,relIndex_subgroupOf hZzT,hl.2,h.field_card]
  have hfix : Nat.card (A ⊓ centralizer (S₀ : Set (Sp F)) : Subgroup (Sp F))=Nat.card F := by
    change Nat.card (A ⊓ centralizer ((S₀ : Subgroup (Sp F)) : Set (Sp F)) : Subgroup (Sp F))=Nat.card F
    rw [hS₀]
    exact (large_sylow_critical_image_fixed_card h d path hb hat hzt c c' S₀ hS₀ hl.1).trans h.field_card.symm
  exact sylow_normal_elementary_square_fixed_ne_field h.field_card h.nonbinary S₀ A hAS hn hA hfix

/-- The first commutator containment in source (3.7)(1) now holds in all
three saturated radical branches, with both complete kernels retained. -/
theorem full_radical_centralizes_critical_images
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) :
    ⁅Z d.radical z,Q d.radical t⁆ ≤ Q d.radical a ∧
      ⁅Z d.radical a,Q d.radical t⁆ ≤ Q d.radical z := by
  rcases marked_radical_elementary_or_sylow h d g (by omega) hsat with he | hs
  · let : IsElementaryAbelian 2 c.action.range := c.action_range.symm ▸ he
    let : IsElementaryAbelian 2 c'.action.range := c'.action_range.symm ▸ he
    have hseed (v : Vertex d.radical) (hv : color d.radical v=false)
        (hvt : Adjacent d.radical v t) : Z d.radical v ≤ Q d.radical t := by
      apply Z_le_Q_of_dist_lt d.radical v (g.exists_critical v hv)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hvt),
        g.distance_constant v hv]
      change 1<g.b d.radical
      omega
    exact ⟨(commutator_mono (hseed z path.end_color hzt) le_rfl).trans
        (c.full_radical_commutator_le_core inferInstance),
      (commutator_mono (hseed a path.start_color hat) le_rfl).trans
        (c'.full_radical_commutator_le_core inferInstance)⟩
  · obtain ⟨S,hS⟩ := hs
    have hS' : (S : Subgroup (Sp F))=c.action.range := hS.trans c.action_range.symm
    have hi := critical_indices_eq_field_of_full_sylow h d path hb hat hzt c c' S hS'
    have hh := full_radical_centralizes_critical_root h d path hb c c' hi.1
    exact ⟨hh.1,hh.2.1⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
