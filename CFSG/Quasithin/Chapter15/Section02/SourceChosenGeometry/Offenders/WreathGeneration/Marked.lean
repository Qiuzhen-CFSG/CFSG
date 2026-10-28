module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefActors.InternalLift
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.WreathGeneration
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# The original marked offender generators

In an S₃ extension with two-group kernel, Sylow conjugacy places a member
of the original conjugacy-stable family in the specified Sylow subgroup.
Its image and the outside actor's image are distinct involutions, so they
generate S₃. The Sylow subgroup normalizes the family span X. Removing
the kernel supplement from its normal span gives I = X join A.
Commutator generation of the cubic residual lifts through the two-group
kernel, giving K_i = [K_i,A] and K_i contained in I.

The source application uses precisely X = <Delta intersect T intersect H_i>
and the original plane-centralizer factor H_i. It proves the source
factor, normal-closure, commutator and full-H generation identities, as well
as normalization of X by N_T(H_i). The order-two chief-action branch places
the original A in H_i and supplies the exact generator witnesses consumed
by sigmaOutside_geometry_of_generation in Offenders.lean.

The order-four image exclusion is still open in qt-e-152-offender-plane;
no order-two premise is asserted to follow from the internal-module lift.
qt-e-152-small-parabolic supplies the preceding action and wreath inputs,
and qt-e-152-plane-geometry retains their final discharge.

Source: Aschbacher--Smith, Notation 15.2.9 and Lemma 15.2.11,
printed pp.1110--1111; refs/quasithin.pdf.
-/

public section
open Subgroup Representation Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

private def movementCubic : SL2 := transvection false * transvection true
private theorem movementCubic_order : movementCubic^3=1 ∧ movementCubic≠1 := by decide +kernel
private theorem movementCubic_commutator : ∀ a : SL2, a^2=1 → a≠1 →
    ⁅movementCubic,a⁆=movementCubic⁻¹ := by decide +kernel

private theorem sl2_residual : pResidual 2 SL2=zpowers movementCubic := by
  have ho : orderOf movementCubic=3 := orderOf_eq_prime movementCubic_order.1 movementCubic_order.2
  have hc : Nat.card SL2=6 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr (mem_pResidual_of_orderOf_coprime (by rw [ho]; decide)))
  rw [card_twoResidual_of_card_six hc,Nat.card_zpowers,ho]

/-- Every nontrivial elementary actor in SL₂(2) generates its cubic residual
by commutators, with no choice of a lift in an extension. -/
theorem sl2_residual_commutator (E : Subgroup SL2) [IsElementaryAbelian 2 E]
    (hE : E≠⊥) : pResidual 2 SL2=⁅pResidual 2 SL2,E⁆ := by
  apply le_antisymm ?_ (commutator_le_left _ _)
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
  have ha2 : (a:SL2)^2=1 := elemPow_eq_one_of_isElementaryAbelian (a:SL2) a.property
  rw [sl2_residual]
  apply zpowers_le.mpr
  have hm := commutator_mem_commutator (mem_zpowers movementCubic) a.property
  rw [movementCubic_commutator a ha2 (fun hh => ha (Subtype.ext hh))] at hm
  simpa using (⁅zpowers movementCubic,E⁆).inv_mem hm

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W}

theorem residualFactor_commutator (c : ChiefWreathCoordinates ρ)
    (hk : IsPGroup 2 c.actor.ker) (i : ChiefWreath.C2)
    (A : Subgroup D) [IsElementaryAbelian 2 A]
    (hA : A ≤ c.factor i) (hn : A.map c.actor≠⊥) :
    c.residualFactor i=⁅c.residualFactor i,A⁆ := by
  let f : c.factor i →* ChiefWreath.SL2 :=
    (ChiefWreath.factorEquiv i).toMonoidHom.comp (c.actor.subgroupComap (ChiefWreath.factor i))
  have hf : Function.Surjective f := (ChiefWreath.factorEquiv i).surjective.comp
    (MonoidHom.subgroupComap_surjective_of_surjective _ _ c.surjective)
  have hfker : IsPGroup 2 f.ker := by
    have heq : f.ker=c.actor.ker.subgroupOf (c.factor i) := by
      ext x
      change (ChiefWreath.factorEquiv i) _=1 ↔ c.actor x=1
      rw [←map_one (ChiefWreath.factorEquiv i), (ChiefWreath.factorEquiv i).injective.eq_iff]
      exact Subtype.ext_iff
    rw [heq]
    exact hk.comap_subtype
  let A₀ := A.subgroupOf (c.factor i)
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hA
  let : IsElementaryAbelian 2 (A₀.map f) := IsElementaryAbelian.map f
  have hne : A₀.map f≠⊥ := by
    intro hz
    apply hn
    apply (map_eq_bot_iff A).mpr
    intro a ha
    have hh := (map_eq_bot_iff A₀).mp hz (show (⟨a,hA ha⟩ : c.factor i)∈A₀ from ha)
    have hh' : c.actor a=1 := by
      have hh' : c.actor.subgroupComap (ChiefWreath.factor i) ⟨a,hA ha⟩ = 1 :=
        (ChiefWreath.factorEquiv i).injective (hh.trans (map_one _).symm)
      exact congrArg Subtype.val hh'
    exact hh'
  have heq := eq_commutator_of_isPPerfect_of_map_eq
    (pResidual 2 (c.factor i)) A₀ (isPPerfect_pResidual 2) le_normalizer_of_normal
    f hfker (by rw [map_pResidual_of_surjective 2 f hf]; exact ChiefWreath.sl2_residual_commutator _ hne)
  have hm := congrArg (Subgroup.map (c.factor i).subtype) heq
  rw [map_commutator,map_subgroupOf_eq_of_le hA] at hm
  exact hm

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath
private theorem two_involution_words : ∀ a b x : SL2,
    a^2=1 → a≠1 → b^2=1 → b≠1 → a≠b →
    x=1 ∨ x=a ∨ x=b ∨ x=a*b ∨ x=b*a ∨ x=a*b*a := by decide +kernel

theorem two_involutions_generate (J : Subgroup SL2) (a b : SL2)
    (ha : a∈J) (hb : b∈J) (ha2 : a^2=1) (han : a≠1)
    (hb2 : b^2=1) (hbn : b≠1) (hab : a≠b) : J=⊤ := by
  apply top_unique
  intro x _
  rcases two_involution_words a b x ha2 han hb2 hbn hab with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem J
  · exact ha
  · exact hb
  · exact mul_mem ha hb
  · exact mul_mem hb ha
  · exact mul_mem (mul_mem ha hb) ha
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
variable {D : Type*} [Group D] [Finite D]

/-- The source X: the subgroup generated by a conjugacy-stable family inside
one specified Sylow subgroup. -/
@[expose] def sylowFamilySpan (F : Set (Subgroup D)) (S : Subgroup D) : Subgroup D :=
  sSup {B | B∈F ∧ B≤S}

omit [Finite D] in
theorem sylowFamilySpan_normalized (F : Set (Subgroup D))
    (hF : ∀ B∈F, ∀ g : D, B.map (MulAut.conj g).toMonoidHom∈F)
    (S : Subgroup D) : S ≤ normalizer (sylowFamilySpan F S : Set D) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hm : (sylowFamilySpan F S).map (MulAut.conj g).toMonoidHom ≤ sylowFamilySpan F S := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    rintro B ⟨hB,hBS⟩
    apply map_le_iff_le_comap.mp
    apply le_sSup
    refine ⟨hF B hB g,?_⟩
    exact (map_mono hBS).trans_eq (mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hg))
  exact hm (mem_map_of_mem _ hx)

/-- Every elementary member is conjugate into the specified Sylow subgroup;
its original marking therefore lies in the normal span of X. -/
theorem family_le_span_sylowFamilySpan (F : Set (Subgroup D))
    (hF : ∀ B∈F, ∀ g : D, B.map (MulAut.conj g).toMonoidHom∈F)
    (S : Sylow 2 D) (A : Subgroup D) [IsElementaryAbelian 2 A] (hA : A∈F) :
    A ≤ conjugateSpanBy (sylowFamilySpan F S) ⊤ := by
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D P S
  have hPS : (P : Subgroup D).map (MulAut.conj g).toMonoidHom = S := by
    change ((g • P : Sylow 2 D) : Subgroup D)=_
    rw [hg]
  have hB : A.map (MulAut.conj g).toMonoidHom ≤ sylowFamilySpan F S :=
    le_sSup ⟨hF A hA g,(map_mono hP).trans_eq hPS⟩
  intro a ha
  have hm := (le_normalizer_conjugateSpanBy (sylowFamilySpan F S) ⊤) (mem_top g⁻¹)
  have hx := (mem_normalizer_iff.mp hm (g*a*g⁻¹)).mp
    ((le_conjugateSpanBy _ _) (hB (mem_map_of_mem _ ha)))
  simpa [mul_assoc] using hx

/-- The marked generation calculation in an S₃ extension. The family stays
literal throughout; only Sylow conjugation and its original members are used. -/
theorem sl2_family_generation (f : D →* ChiefWreath.SL2)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (F : Set (Subgroup D))
    (hF : ∀ B∈F, ∀ g : D, B.map (MulAut.conj g).toMonoidHom∈F)
    (S : Sylow 2 D) (A : Subgroup D) [IsElementaryAbelian 2 A]
    (hA : A∈F) (hAS : ¬ A ≤ S) :
    let X := sylowFamilySpan F S
    f.ker ⊔ (X ⊔ A)=⊤ ∧ conjugateSpanBy X ⊤=X ⊔ A ∧
      pResidual 2 D ≤ X ⊔ A ∧ pResidual 2 D=⁅pResidual 2 D,A⁆ := by
  let X := sylowFamilySpan F S
  let J := X ⊔ A
  let I := conjugateSpanBy X ⊤
  have hKS : f.ker≤S := hk.le_sylow_of_normal S
  have hAI : A≤I := family_le_span_sylowFamilySpan F hF S A hA
  have hXI : X≤I := le_conjugateSpanBy _ _
  have hXN : (S : Subgroup D) ≤ normalizer (X : Set D) := sylowFamilySpan_normalized F hF S
  have hAn : A.map f≠⊥ := by
    intro hz
    exact hAS (((map_eq_bot_iff A).mp hz).trans hKS)
  obtain ⟨a,ha,has⟩ : ∃ a∈A, f a∉(S : Subgroup D).map f := by
    by_contra! hn
    have hm : A.map f ≤ (S : Subgroup D).map f := by
      rintro _ ⟨a,ha,rfl⟩
      exact hn a ha
    have hh := Subgroup.map_le_map_iff.mp hm
    rw [sup_eq_left.mpr hKS] at hh
    exact hAS hh
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D P S
  have hPS : (P : Subgroup D).map (MulAut.conj g).toMonoidHom = S := by
    change ((g • P : Sylow 2 D) : Subgroup D)=_
    rw [hg]
  let B := A.map (MulAut.conj g).toMonoidHom
  have hBX : B≤X := le_sSup ⟨hF A hA g,(map_mono hP).trans_eq hPS⟩
  have hBS : B≤S := (map_mono hP).trans_eq hPS
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hbn : f (g*a*g⁻¹)≠1 := by
    intro hh
    have hh' : f a=1 := by
      have ht := congrArg (fun z => (f g)⁻¹*z*f g) hh
      simpa [map_mul,map_inv,mul_assoc] using ht
    exact has (hh'.symm ▸ one_mem _)
  let b := g*a*g⁻¹
  have hbB : b∈B := mem_map_of_mem _ ha
  have hmap : J.map f=⊤ := by
    apply ChiefWreath.two_involutions_generate _ (f a) (f b)
      (mem_map_of_mem _ ((le_sup_right : A≤J) ha))
      (mem_map_of_mem _ ((hBX.trans le_sup_left) hbB))
    · rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian a ha,map_one]
    · intro hh
      exact has (hh.symm ▸ one_mem _)
    · rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian b hbB,map_one]
    · exact hbn
    · intro hh
      exact has (hh.symm ▸ mem_map_of_mem f (hBS hbB))
  have hgen : f.ker ⊔ J=⊤ := by
    have hh : (⊤ : Subgroup D).map f≤J.map f := by rw [hmap]; exact le_top
    have hh' := Subgroup.map_le_map_iff.mp hh
    simpa [sup_comm] using top_unique hh'
  have hIJ : I=J := by
    apply le_antisymm ?_ (sup_le hXI hAI)
    apply (closure_le _).mpr
    rintro _ ⟨k,_,x,hx,rfl⟩
    have hkJ : k∈J ⊔ f.ker := by rw [sup_comm,hgen]; trivial
    obtain ⟨j,hj,q,hq,rfl⟩ := mem_sup_of_normal_right.mp hkJ
    have hqx : q*x*q⁻¹∈X := (mem_normalizer_iff.mp (hXN (hKS hq)) x).mp hx
    have hh := (mem_normalizer_iff.mp (J.le_normalizer hj) (q*x*q⁻¹)).mp
      ((le_sup_left : X≤J) hqx)
    simpa [mul_assoc] using hh
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hcomm : pResidual 2 D=⁅pResidual 2 D,A⁆ :=
    eq_commutator_of_isPPerfect_of_map_eq _ A (isPPerfect_pResidual 2)
      le_normalizer_of_normal f hk (by
        rw [map_pResidual_of_surjective 2 f hf]
        exact ChiefWreath.sl2_residual_commutator _ hAn)
  have hnormal : I.Normal := normalizer_eq_top_iff.mp (top_unique (le_normalizer_conjugateSpanBy X ⊤))
  let := hnormal
  have hres : pResidual 2 D≤I := by
    rw [hcomm]
    exact (commutator_mono le_rfl hAI).trans (commutator_le_right _ _)
  exact ⟨hgen,hIJ,hres.trans_eq hIJ,hcomm⟩
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W}

omit [Finite D] in
theorem factor_subnormal (c : ChiefWreathCoordinates ρ) (i : ChiefWreath.C2) :
    (c.factor i).IsSubnormal := by
  let B := ChiefWreath.base.comap c.actor
  let : B.Normal := by
    change ((RegularWreathProduct.rightHom.comp c.actor).ker).Normal
    infer_instance
  exact IsSubnormal.step _ B (c.factor_le_base i) (inferInstance : B.Normal).isSubnormal
    (normal_subgroupOf_of_le_normalizer (c.base_normalizes_factor i))
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates

namespace CFSG.Quasithin.Chapter15.Section02
open Subgroup Stellmacher Representation Representation.BinaryOffender NoncentralChiefRefinement Theory.GroupTheory
open ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor SmallActionsSource
variable {G : Type*} [Group G] [Finite G]

/-- The exact marked family generated in the proof of 15.2.11. -/
@[expose] def markedOffenderSpan (T H L : Subgroup G) : Subgroup G :=
  sSup {B | B∈delta H ∧ B≤T ∧ B≤L}

/-- The marked generation argument for an original offender once it is placed
in the distinguished factor. The factor placement is supplied by the order-two
branch; it is not replaced by an arbitrary wreath isomorphism. -/
theorem ChosenSmallSource.marked_offender_generation
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} (c : ChiefWreathCoordinates ρ)
    (hc : c.actor.ker=pCore 2 H) (i : ChiefWreath.C2)
    (hA : A∈delta H) (hAi : A.subgroupOf H ≤ c.factor i)
    (hAT : ¬ A≤(T : Subgroup G)) :
    let L := (c.factor i).map H.subtype
    let K := (c.residualFactor i).map H.subtype
    let X := markedOffenderSpan (T : Subgroup G) H L
    X ≤ centralizer (V : Set G) ∧
      L=twoCoreIn H ⊔ (X ⊔ A) ∧
      conjugateSpanBy X L=X ⊔ A ∧ K≤X ⊔ A ∧ K=⁅K,A⁆ ∧
      H=(X ⊔ A) ⊔ (T : Subgroup G) ∧
      ChosenGeometry.residual H=conjugateSpanBy K H := by
  let L₀ := c.factor i
  let L := L₀.map H.subtype
  let α : L₀ →* G := H.subtype.comp L₀.subtype
  let F : Set (Subgroup L₀) := {B | B.map α∈delta H}
  have hF : ∀ B∈F, ∀ g : L₀, B.map (MulAut.conj g).toMonoidHom∈F := by
    intro B hB g
    have hh := delta_conjugate hB g.val.property
    have hm : α.comp (MulAut.conj g).toMonoidHom = (MulAut.conj (α g)).toMonoidHom.comp α := by
      ext x
      simp [MulAut.conj_apply]
    change (B.map _).map α∈delta H
    rw [map_map,hm,←map_map]
    exact hh
  obtain ⟨S,hS⟩ := (T.subtype hH.1.1.2).exists_subgroupOf_eq_of_subnormal L₀ (c.factor_subnormal i)
  have hSval (x : L₀) : x∈(S : Subgroup L₀) ↔ α x∈(T : Subgroup G) := by
    rw [hS]
    rfl
  let A₀ := (A.subgroupOf H).subgroupOf L₀
  have hAm : A₀.map α=A := by
    dsimp only [α]
    rw [←map_map,map_subgroupOf_eq_of_le hAi,map_subgroupOf_eq_of_le hA.1.1]
  have hA₀F : A₀∈F := by change A₀.map α∈delta H; rwa [hAm]
  let : IsElementaryAbelian 2 A := hA.1.2.1
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hA.1.1
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hAi
  have hA₀S : ¬ A₀≤(S : Subgroup L₀) := by
    intro hh
    apply hAT
    rw [←hAm]
    rintro _ ⟨x,hx,rfl⟩
    exact (hSval x).mp (hh hx)
  let f : L₀ →* ChiefWreath.SL2 :=
    (ChiefWreath.factorEquiv i).toMonoidHom.comp (c.actor.subgroupComap (ChiefWreath.factor i))
  have hf : Function.Surjective f := (ChiefWreath.factorEquiv i).surjective.comp
    (MonoidHom.subgroupComap_surjective_of_surjective _ _ c.surjective)
  have hfker : f.ker=(pCore 2 H).subgroupOf L₀ := by
    rw [←hc]
    ext x
    change (ChiefWreath.factorEquiv i) _=1 ↔ c.actor x=1
    rw [←map_one (ChiefWreath.factorEquiv i), (ChiefWreath.factorEquiv i).injective.eq_iff]
    exact Subtype.ext_iff
  have hkp : IsPGroup 2 f.ker := by rw [hfker]; exact pCore_isPGroup.comap_subtype
  obtain ⟨hgen,hspan,hres,hcomm⟩ := sl2_family_generation f hf hkp F hF S A₀ hA₀F hA₀S
  let X₀ := sylowFamilySpan F S
  let X := markedOffenderSpan (T : Subgroup G) H L
  have hXm : X₀.map α=X := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      rintro B ⟨hB,hBS⟩
      apply map_le_iff_le_comap.mp
      apply le_sSup
      refine ⟨hB,?_,?_⟩
      · rintro _ ⟨b,hb,rfl⟩
        exact (hSval b).mp (hBS hb)
      · rintro _ ⟨b,hb,rfl⟩
        exact mem_map_of_mem H.subtype b.property
    · apply sSup_le
      rintro B ⟨hB,hBT,hBL⟩
      have hBi : B.subgroupOf H≤L₀ := by
        intro b hb
        obtain ⟨x,hx,hxb⟩ := hBL hb
        exact H.subtype_injective hxb ▸ hx
      let B₀ := (B.subgroupOf H).subgroupOf L₀
      have hBm : B₀.map α=B := by
        dsimp only [α]
        rw [←map_map,map_subgroupOf_eq_of_le hBi,map_subgroupOf_eq_of_le hB.1.1]
      rw [←hBm]
      apply map_mono
      apply le_sSup
      refine ⟨?_,?_⟩
      · change B₀.map α∈delta H
        rwa [hBm]
      · intro b hb
        exact (hSval b).mpr (hBT hb)
  have hQL : pCore 2 H≤L₀ := by
    rw [←hc]
    exact comap_mono bot_le
  have hKm : (pResidual 2 L₀).map α=(c.residualFactor i).map H.subtype := by
    exact (Subgroup.map_map _ _ _).symm
  have hQm : f.ker.map α=twoCoreIn H := by
    dsimp only [α]
    rw [hfker,←map_map,map_subgroupOf_eq_of_le hQL]
    rfl
  have htop : (⊤ : Subgroup L₀).map α=L := by
    dsimp only [α]
    rw [←map_map,←MonoidHom.range_eq_map,range_subtype]
  have hXV : X≤centralizer (V : Set G) := by
    apply sSup_le
    rintro B ⟨hB,hBT,_⟩
    have hmax : B∈elementaryAbelianMaxSubgroups (T : Subgroup G) :=
      ⟨hBT,hB.1.2.1,fun C hCT he => hB.1.2.2 C (hCT.trans hH.1.1.2) he⟩
    exact (le_sSup hmax).trans (h.centralizing.trans (centralizer_le h.prepared.le_local))
  refine ⟨hXV,?_,?_,?_,?_,?_,?_⟩
  · have hh := congrArg (Subgroup.map α) hgen
    rw [Subgroup.map_sup,Subgroup.map_sup,hQm,hXm,hAm,htop] at hh
    exact hh.symm
  · have hh := congrArg (Subgroup.map α) hspan
    rw [map_conjugateSpanBy,Subgroup.map_sup,hXm,htop,hAm] at hh
    exact hh
  · have hh := map_mono (f:=α) hres
    rwa [hKm,Subgroup.map_sup,hXm,hAm] at hh
  · have hh := congrArg (Subgroup.map α) hcomm
    rwa [hKm,map_commutator,hKm,hAm] at hh
  · apply le_antisymm ?_ (sup_le (sup_le ?_ hA.1.1) hH.1.1.2)
    · exact (h.offender_sup_sylow_eq hH he hA.1.1 hAT).ge.trans
        (sup_le_sup le_sup_right le_rfl)
    · apply sSup_le
      rintro B ⟨hB,_,_⟩
      exact hB.1.1
  · have hh := congrArg (Subgroup.map H.subtype) (c.residualFactor_span i)
    rw [map_conjugateSpanBy,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm
end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02
open Subgroup Stellmacher Representation Representation.BinaryOffender NoncentralChiefRefinement Theory.GroupTheory
open ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor SmallActionsSource
variable {G : Type*} [Group G] [Finite G]

/-- Source 15.2.11's marked generators in the order-two branch, on any one
of the actual noncentral chief factors. Only the order-four exclusion remains
between this theorem and the uniform marked conclusion. -/
theorem ChosenSmallSource.delta_two_marked_generation
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A∈delta H) (htwo : Nat.card (offenderImage H A)=2)
    (hAT : ¬ A≤(T : Subgroup G))
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (j : Fin s.series.length) (hj : ¬ s.Central j)
    (c : ChiefWreathCoordinates (s.factorRepresentation j)) :
    ∃ i : ChiefWreath.C2, A.subgroupOf H≤c.factor i ∧
      let L := (c.factor i).map H.subtype
      let K := (c.residualFactor i).map H.subtype
      let X := markedOffenderSpan (T : Subgroup G) H L
      X ≤ centralizer (V : Set G) ∧
        L=twoCoreIn H ⊔ (X ⊔ A) ∧
        conjugateSpanBy X L=X ⊔ A ∧ K≤X ⊔ A ∧ K=⁅K,A⁆ ∧
        H=(X ⊔ A) ⊔ (T : Subgroup G) ∧
        ChosenGeometry.residual H=conjugateSpanBy K H := by
  obtain ⟨i,hi,_⟩ := h.delta_two_chief_factor hunique hH he hA htwo s j hj c
  exact ⟨i,hi,h.marked_offender_generation hH he c
    (c.kernel.trans (h.chief_kernel_of_residual_unique hunique hH s j hj)) i hA hi hAT⟩
end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02
open Subgroup Stellmacher Representation Representation.BinaryOffender NoncentralChiefRefinement Theory.GroupTheory
open ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor SmallActionsSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The source X is normalized by the literal normalizer of its marked factor
inside T. This follows from conjugacy invariance of the original Delta family. -/
theorem markedOffenderSpan_normalized (T H L : Subgroup G) (hTH : T≤H) :
    T ⊓ normalizer (L : Set G) ≤ normalizer (markedOffenderSpan T H L : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hm : (markedOffenderSpan T H L).map (MulAut.conj g).toMonoidHom ≤
      markedOffenderSpan T H L := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    rintro B ⟨hB,hBT,hBL⟩
    apply map_le_iff_le_comap.mp
    apply le_sSup
    refine ⟨delta_conjugate hB (hTH hg.1),?_,?_⟩
    · exact (map_mono hBT).trans_eq (mem_normalizer_iff_map_conj_eq.mp (T.le_normalizer hg.1))
    · exact (map_mono hBL).trans_eq (mem_normalizer_iff_map_conj_eq.mp hg.2)
  exact hm (mem_map_of_mem _ hx)

/-- Actual witnesses for the marked plane-normality consumer, assuming only
the still-open order-two clause for this original outside offender. The
Sylow family X and residual K retain their source markings in the construction. -/
theorem ChosenSmallSource.delta_two_generator_witnesses
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hA : A∈delta H) (htwo : Nat.card (offenderImage H A)=2)
    (hAT : ¬ A≤(T : Subgroup G)) :
    ∃ X K : Subgroup G, X≤centralizer (V : Set G) ∧
      H=(X ⊔ A) ⊔ (T : Subgroup G) ∧ K≤X ⊔ A ∧
      ChosenGeometry.residual H=conjugateSpanBy K H := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V≤H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hi,hj,c,d,hc,hd,hb⟩ := h.two_chief_coordinates_with_common_base hunique hH he s
  obtain ⟨k,hk,hXV,hL,hI,hK,hKA,hgen,hspan⟩ :=
    h.delta_two_marked_generation hunique hH he hA htwo hAT s i hi c
  exact ⟨_,_,hXV,hgen,hK,hspan⟩
end CFSG.Quasithin.Chapter15.Section02
