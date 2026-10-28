module
public import Theory.GroupTheory.QuaternionSwapModel.DiagonalCubic
public import Theory.GroupTheory.CentralCoprimeCardLift
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# A residual diagonal mover from one quaternion cubic

An injected quaternion-swap subgroup retains its two quaternion factors,
central line, elementary sixteen, and marked plane. A cubic actor on just
the first factor has a swap-conjugate acting on just the second factor.
Their commutator centralizes the whole quaternion product and is central
of order dividing two. Coprime torsion lifting makes the two actors commute.
Their product therefore fixes the actual swap and induces the same
nontrivial cubic on both factors. It lies in the two-residual, normalizes
the sixteen, and moves the marked plane.

The final theorem assumes only self-centralization of the quaternion product
and centrality of its marked line, exactly as supplied by the characteristic-
two overgroup in the Aut(M₁₂) row of Aschbacher--Smith, Lemma 14.2.21,
printed p.988. No recognition of the full enlarged residual is required.
-/

public section
open Subgroup
namespace QuaternionSwapModel
open MarkedCubic
variable {D : Type*} [Group D]

private theorem commute_of_opposite_factor_actions (B C Z : Subgroup D)
    (hZ : Z ≤ center D) (hZcard : Nat.card Z = 2)
    (hc : centralizer ((B ⊔ C : Subgroup D) : Set D) ≤ Z)
    (u v : D) (hu3 : u ^ 3 = 1)
    (huB : u ∈ normalizer (B : Set D)) (huC : u ∈ centralizer (C : Set D))
    (hvC : v ∈ normalizer (C : Set D)) (hvB : v ∈ centralizer (B : Set D)) :
    Commute u v := by
  let Znormal : Z.Normal := ⟨fun z hz x => by
    simpa only [mem_center_iff.mp (hZ hz) x,mul_inv_cancel_right] using hz⟩
  let q := QuotientGroup.mk' Z
  have hw : u*v*u⁻¹*v⁻¹ ∈ Z := by
    apply hc
    have hB : u*v*u⁻¹*v⁻¹ ∈ centralizer (B : Set D) := by
      apply (centralizer (B : Set D)).mul_mem
      · exact (mem_normalizer_iff.mp ((normalizer_le_normalizer_centralizer B) huB) v).mp hvB
      · exact (centralizer (B : Set D)).inv_mem hvB
    have hC : u*v*u⁻¹*v⁻¹ ∈ centralizer (C : Set D) := by
      have hh := (mem_normalizer_iff.mp ((normalizer_le_normalizer_centralizer C) hvC) u⁻¹).mp
        ((centralizer (C : Set D)).inv_mem huC)
      have hm := (centralizer (C : Set D)).mul_mem huC hh
      simpa only [mul_assoc] using hm
    have hBC : B ⊔ C ≤ centralizer ({u*v*u⁻¹*v⁻¹} : Set D) := by
      apply sup_le
      · exact fun b hb => mem_centralizer_singleton_iff.mpr (hB b hb)
      · exact fun b hb => mem_centralizer_singleton_iff.mpr (hC b hb)
    intro b hb
    exact mem_centralizer_singleton_iff.mp (hBC hb)
  have hcomm : Commute (q u) (q v) := by
    have hh : q (u*v*u⁻¹*v⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hw
    have he := congrArg (fun x => x * q v * q u) hh
    change q u * q v = q v * q u
    simpa only [map_mul,map_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one,one_mul] using he
  apply q.commute_of_map_commute_of_pow_eq_one_of_central_coprime_ker _ _ hu3 hcomm
  · simpa only [q,QuotientGroup.ker_mk'] using hZ
  · change (Nat.card (QuotientGroup.mk' Z).ker).Coprime 3
    rw [QuotientGroup.ker_mk',hZcard]
    decide

/-- A cubic acting on one quaternion factor produces a diagonal cubic on
both factors and the unchanged swapping involution. -/
theorem exists_diagonal_cubic_action
    (f : QH →* D) (hf : Function.Injective f)
    (hc : centralizer (QK.map f : Set D) ≤ Z.map f)
    (hZ : Z.map f ≤ center D)
    (u : D) (hu : orderOf u = 3)
    (huB : u ∈ normalizer (leftFactor.map f : Set D))
    (huC : u ∈ centralizer (rightFactor.map f : Set D))
    (hune : u ∉ centralizer (leftFactor.map f : Set D)) :
    ∃ g : D, g ∈ pResidual 2 D ∧ ∃ a : MulAut (QuaternionGroup 2),
      a ^ 3 = 1 ∧ a ≠ 1 ∧ ∀ x : QH, g*f x*g⁻¹ = f (qhAut a x) := by
  let B := leftFactor.map f
  let C := rightFactor.map f
  let l := f.comp leftEmbedding
  let r := f.comp rightEmbedding
  have hl : Function.Injective l := hf.comp leftEmbedding_injective
  have hr : Function.Injective r := hf.comp rightEmbedding_injective
  let eB : QuaternionGroup 2 ≃* B :=
    (MonoidHom.ofInjective hl).trans (MulEquiv.subgroupCongr (MonoidHom.range_comp f leftEmbedding))
  let a : MulAut (QuaternionGroup 2) :=
    (MulAut.congr eB.symm) (B.normalizerMonoidHom ⟨u,huB⟩)
  have ha (q : QuaternionGroup 2) : u*l q*u⁻¹ = l (a q) := by
    have hh := eB.apply_symm_apply (B.normalizerMonoidHom ⟨u,huB⟩ (eB q))
    exact (congrArg Subtype.val hh).symm
  have ha3 : a ^ 3 = 1 := by
    change ((MulAut.congr eB.symm) (B.normalizerMonoidHom ⟨u,huB⟩))^3 = 1
    rw [← map_pow,← map_pow]
    have hu3 : (⟨u,huB⟩ : normalizer (B : Set D))^3 = 1 := by
      apply Subtype.ext
      exact hu ▸ pow_orderOf_eq_one u
    rw [hu3,map_one,map_one]
  have hane : a ≠ 1 := by
    intro he
    apply hune
    rintro _ ⟨_,⟨q,rfl⟩,rfl⟩
    have hh := ha q
    rw [he] at hh
    change u*l q*u⁻¹ = l q at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let s := f swap
  have hs : s*s = 1 := by
    change f swap*f swap=1
    rw [← map_mul,← pow_two,swap_square,map_one]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hss (x : D) : s*(s*x)=x := by rw [← mul_assoc,hs,one_mul]
  have hsl (q : QuaternionGroup 2) : s*l q*s = r q := by
    have hh := congrArg f (swap_left q)
    simp only [map_mul,map_inv] at hh
    change s*l q*s⁻¹=r q at hh
    rwa [hsinv] at hh
  have hsr (q : QuaternionGroup 2) : s*r q*s = l q := by
    rw [← hsl q]
    calc
      s*(s*l q*s)*s = (s*s)*l q*(s*s) := by group
      _ = l q := by rw [hs]; simp
  let v := s*u*s
  have hvB : v ∈ centralizer (B : Set D) := by
    rintro _ ⟨_,⟨q,rfl⟩,rfl⟩
    have hh := huC (r q) ⟨rightEmbedding q,⟨q,rfl⟩,rfl⟩
    change l q*v=v*l q
    calc
      l q*v = s*(r q*u)*s := by dsimp [v]; rw [← hsr q]; simp only [mul_assoc,hss]
      _ = s*(u*r q)*s := by rw [hh]
      _ = v*l q := by dsimp [v]; rw [← hsr q]; simp only [mul_assoc,hss]
  have hv (q : QuaternionGroup 2) : v*r q*v⁻¹ = r (a q) := by
    calc
      v*r q*v⁻¹ = s*(u*(s*r q*s)*u⁻¹)*s := by dsimp [v]; simp only [mul_inv_rev,hsinv,mul_assoc]
      _ = s*(u*l q*u⁻¹)*s := by rw [hsr]
      _ = r (a q) := by rw [ha,hsl]
  have hvC : v ∈ normalizer (C : Set D) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro _ ⟨_,⟨_,⟨q,rfl⟩,rfl⟩,rfl⟩
      change v*r q*v⁻¹ ∈ C
      rw [hv]
      exact ⟨rightEmbedding (a q),⟨a q,rfl⟩,rfl⟩
    · rintro _ ⟨_,⟨q,rfl⟩,rfl⟩
      refine ⟨r (a.symm q),⟨rightEmbedding (a.symm q),⟨a.symm q,rfl⟩,rfl⟩,?_⟩
      change v*r (a.symm q)*v⁻¹=r q
      simpa only [a.apply_symm_apply] using hv (a.symm q)
  have hu3 : u^3=1 := hu ▸ pow_orderOf_eq_one u
  have huv : Commute u v := commute_of_opposite_factor_actions B C (Z.map f) hZ
    (by rw [card_map_of_injective hf,card_Z])
    (by simpa only [QK,Subgroup.map_sup] using hc) u v hu3 huB huC hvC hvB
  let g := u*v
  have hgS : g*s*g⁻¹=s := by
    have hvu : s*v*s=u := by dsimp [v]; calc
      s*(s*u*s)*s=(s*s)*u*(s*s) := by group
      _=u := by rw [hs];simp
    have hh : s*g*s=g := by
      calc
        s*g*s=(s*u*s)*(s*v*s) := by dsimp [g]; simp only [mul_assoc,hss]
        _=v*u := by rw [hvu]
        _=g := huv.symm.eq
    have hcomm : s*g=g*s := by
      have h := congrArg (fun x => x*s) hh
      simpa only [mul_assoc,hs,mul_one] using h
    rw [← hcomm,mul_assoc,mul_inv_cancel,mul_one]
  have hgL (q : QuaternionGroup 2) : g*l q*g⁻¹=l (a q) := by
    calc
      g*l q*g⁻¹=u*(v*l q*v⁻¹)*u⁻¹ := by dsimp [g];group
      _=u*l q*u⁻¹ := by rw [← hvB (l q) ⟨leftEmbedding q,⟨q,rfl⟩,rfl⟩,mul_inv_cancel_right]
      _ = l (a q) := ha q
  have hgR (q : QuaternionGroup 2) : g*r q*g⁻¹=r (a q) := by
    calc
      g*r q*g⁻¹=u*(v*r q*v⁻¹)*u⁻¹ := by dsimp [g];group
      _=u*r (a q)*u⁻¹ := by rw [hv]
      _ = r (a q) := by rw [← huC (r (a q)) ⟨rightEmbedding (a q),⟨a q,rfl⟩,rfl⟩,mul_inv_cancel_right]
  have hact : (MulAut.conj g).toMonoidHom.comp f = f.comp (qhAut a).toMonoidHom := by
    apply hom_ext_factors_swap
    · intro q
      change g*l q*g⁻¹ = f (qhAut a (leftEmbedding q))
      rw [qhAut_left]
      exact hgL q
    · intro q
      change g*r q*g⁻¹ = f (qhAut a (rightEmbedding q))
      rw [qhAut_right]
      exact hgR q
    · change g*s*g⁻¹ = f (qhAut a swap)
      rw [qhAut_swap]
      exact hgS
  have huRes : u ∈ pResidual 2 D := mem_pResidual_of_orderOf_coprime (by rw [hu];decide)
  have hvRes : v ∈ pResidual 2 D := by
    have hh := (inferInstance : (pResidual 2 D).Normal).conj_mem u huRes s
    simpa only [hsinv] using hh
  exact ⟨g,(pResidual 2 D).mul_mem huRes hvRes,a,ha3,hane,fun x => DFunLike.congr_fun hact x⟩


/-- The moving residual element preserves the actual elementary sixteen and
moves the specified plane, with only self-centralization of the quaternion core. -/
theorem exists_residual_plane_mover
    (f : QH →* D) (hf : Function.Injective f)
    (hc : centralizer (QK.map f : Set D) ≤ QK.map f)
    (hZ : Z.map f ≤ center D)
    (u : D) (hu : orderOf u = 3)
    (huB : u ∈ normalizer (leftFactor.map f : Set D))
    (huC : u ∈ centralizer (rightFactor.map f : Set D))
    (hune : u ∉ centralizer (leftFactor.map f : Set D)) :
    ∃ g : D, g ∈ pResidual 2 D ∧ g ∈ normalizer (A.map f : Set D) ∧
      (markedPlane.map f).map (MulAut.conj g).toMonoidHom ≠ markedPlane.map f := by
  have hcZ : centralizer (QK.map f : Set D) ≤ Z.map f := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := hc hx
    have hqZ : q ∈ Z := by
      rw [← core_center_image]
      refine ⟨⟨q,hq⟩,mem_center_iff.mpr (fun y => ?_),rfl⟩
      apply Subtype.ext
      apply hf
      change f ((y : QH)*q) = f (q*(y : QH))
      simpa only [map_mul] using hx (f y) ⟨y,y.property,rfl⟩
    exact ⟨q,hqZ,rfl⟩
  obtain ⟨g,hg,a,ha,hane,hact⟩ := exists_diagonal_cubic_action f hf hcZ hZ u hu huB huC hune
  have hhom : (MulAut.conj g).toMonoidHom.comp f = f.comp (qhAut a).toMonoidHom :=
    MonoidHom.ext hact
  have hA : A.map (qhAut a).toMonoidHom = A := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact qhAut_mem_A a x hx
    · intro x hx
      refine ⟨(qhAut a).symm x,?_,(qhAut a).apply_symm_apply x⟩
      have hh := qhAut_mem_A a⁻¹ x hx
      have he : qhAut a⁻¹ = (qhAut a)⁻¹ := map_inv qhAutHom a
      rw [he] at hh
      exact hh
  refine ⟨g,hg,mem_normalizer_iff_map_conj_eq.mpr ?_,?_⟩
  · change (A.map f).map (MulAut.conj g).toMonoidHom = A.map f
    rw [Subgroup.map_map,hhom,← Subgroup.map_map,hA]
  · intro he
    rw [Subgroup.map_map,hhom,← Subgroup.map_map] at he
    exact qhAut_moves_markedPlane a ha hane
      (map_injective hf he)


end QuaternionSwapModel
