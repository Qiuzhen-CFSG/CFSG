module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.ElementarySylow
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.PlaneExchange
public import Theory.GroupTheory.SylowElementaryIncidence
/-!
# Fusion controlled by the actual sixteen-group normalizers

The two elementary sixteen-groups exhaust an ambient Sylow. The marked
root normalizer supplies an interchange fixing any point of their common
four-group. Sylow conjugacy inside a point centralizer therefore gives
ambient incidence transitivity, and hence normalizer control of element
fusion. The original one-class hypothesis makes each full normalizer
transitive on its fifteen nonidentity points. In particular it contains
an element moving the distinguished involution outside the root center.

Source: Aschbacher, *Sporadic Groups* (1994), 46.14(4–5a), pp.257–258.
No two-class census or ambient J₃ recognition is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.HyperbolicRecognition
namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
open Matrix.PSL3Four
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
namespace ReturningPair
variable (P : ReturningPair D)

private theorem marked_actor_conjugation
    (d : P.R ≃* RootNormalizerModel.Root)
    (f : normalizer (P.R : Set G) ≃* RootNormalizerModel.Model)
    (hf : ∀ r : P.R, f (inclusion le_normalizer r) = SemidirectProduct.inl (d r))
    (s : RootNormalizerModel.actor) (q : RootNormalizerModel.Root) :
    MulAut.conj (f.symm (SemidirectProduct.inr s) : G) (d.symm q : G) =
      (d.symm ((s : MulAut RootNormalizerModel.Root) q) : G) := by
  have hmark (q : RootNormalizerModel.Root) :
      f.symm (SemidirectProduct.inl q) = inclusion le_normalizer (d.symm q) := by
    apply f.injective
    rw [f.apply_symm_apply,hf,d.apply_symm_apply]
  have h := congrArg (fun x : RootNormalizerModel.Model => (f.symm x : G))
    (SemidirectProduct.inl_aut (φ := RootNormalizerModel.actor.subtype) s q)
  simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv,hmark] at h
  exact h.symm

theorem exchange_marked_planes
    (d : P.R ≃* RootNormalizerModel.Root)
    (f : normalizer (P.R : Set G) ≃* RootNormalizerModel.Model)
    (hf : ∀ r : P.R, f (inclusion le_normalizer r) = SemidirectProduct.inl (d r))
    (z : G) (hz : z ∈ P.E) :
    ∃ c ∈ centralizer ({z} : Set G), c ∈ normalizer (P.R : Set G) ∧
      (P.A₁ d).conjBy c = P.A₂ d ∧ (P.A₂ d).conjBy c = P.A₁ d := by
  obtain ⟨zR,hzR,hzval⟩ := (Geometry.E_center P).symm ▸ hz
  have hzmodel : d zR ∈ center RootNormalizerModel.Root := by
    rw [mem_center_iff]
    intro q
    obtain ⟨r,rfl⟩ := d.surjective q
    simpa only [map_mul] using congrArg d ((mem_center_iff.mp hzR) r)
  obtain ⟨s,hs,hs₁,hs₂⟩ := RootNormalizerModel.exists_exchange_fixing_center (d zR) hzmodel
  let c : G := f.symm (SemidirectProduct.inr s)
  have hact := P.marked_actor_conjugation d f hf s
  have hcfix : MulAut.conj c z = z := by
    rw [←hzval]
    change MulAut.conj (f.symm (SemidirectProduct.inr s) : G) (zR : G) = (zR : G)
    have hh := hact (d zR)
    simpa only [d.symm_apply_apply,hs] using hh
  have hplane (A B : Subgroup RootNormalizerModel.Root)
      (hAB : A.map (s : MulAut RootNormalizerModel.Root).toMonoidHom = B) :
      ((A.map d.symm.toMonoidHom).map P.R.subtype).conjBy c =
        (B.map d.symm.toMonoidHom).map P.R.subtype := by
    rw [←hAB]
    simp only [Subgroup.conjBy,map_map]
    congr 1
    ext q
    exact hact q
  exact ⟨c,mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hcfix),
    (f.symm (SemidirectProduct.inr s)).property,
    hplane rootPlane₁ rootPlane₂ hs₁,hplane rootPlane₂ rootPlane₁ hs₂⟩

include P in
/-- The normalizer of every elementary sixteen-group controls its ambient element fusion. -/
theorem elementary_sixteen_normalizer_fusion (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (x y : G) (hx : x ∈ A) (hy : y ∈ A) (hxy : IsConj x y) :
    ∃ c ∈ normalizer (A : Set G), MulAut.conj c x = y := by
  obtain ⟨d,f,hf⟩ := Geometry.Normalizer.exists_identification P
  obtain ⟨S,hRS,hSN,hS⟩ := P.exists_ambient_sylow hclass
  apply S.elementary_normalizer_controls_fusion_of_local (n := 16) ?_ A hA x y hx hy hxy
  intro U V hU hV hUS hVS hUc hVc z hzU hzV
  have hU' := (P.elementary_sixteen_in_sylow_iff d S hRS hSN hS U hUS).mp ⟨hU,hUc⟩
  have hV' := (P.elementary_sixteen_in_sylow_iff d S hRS hSN hS V hVS).mp ⟨hV,hVc⟩
  rcases hU' with rfl | rfl <;> rcases hV' with rfl | rfl
  · exact ⟨1,one_mem _,conjBy_one _⟩
  · have hzE : z ∈ P.E := P.planes_inf d ▸ (show z ∈ P.A₁ d ⊓ P.A₂ d from ⟨hzU,hzV⟩)
    obtain ⟨c,hc,_,he,_⟩ := P.exchange_marked_planes d f hf z hzE
    exact ⟨c,hc,he⟩
  · have hzE : z ∈ P.E := P.planes_inf d ▸ (show z ∈ P.A₁ d ⊓ P.A₂ d from ⟨hzV,hzU⟩)
    obtain ⟨c,hc,_,_,he⟩ := P.exchange_marked_planes d f hf z hzE
    exact ⟨c,hc,he⟩
  · exact ⟨1,one_mem _,conjBy_one _⟩

include P in
/-- In the one-class branch the full normalizer is transitive on the fifteen nonidentity points. -/
theorem elementary_sixteen_normalizer_transitive (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (x y : G) (hx : x ∈ A) (hy : y ∈ A) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ c ∈ normalizer (A : Set G), MulAut.conj c x = y := by
  apply P.elementary_sixteen_normalizer_fusion hclass A hA x y hx hy
  exact hclass.isConj
    (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian y hy) hy1)
    (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hx1)

/-- Each full plane normalizer contains an actual element moving z outside E;
therefore it is not contained in the root normalizer. -/
theorem plane_normalizer_escapes (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hEA : P.E ≤ A) :
    ∃ c ∈ normalizer (A : Set G),
      MulAut.conj c D.z ∉ P.E ∧ c ∉ normalizer (P.R : Set G) := by
  have hnot : ¬ A ≤ P.E := by
    intro h
    have hh := card_le_of_le h
    rw [hA,P.E_card] at hh
    omega
  obtain ⟨a,ha,haE⟩ := SetLike.not_le_iff_exists.mp hnot
  have hz1 : D.z ≠ 1 := by
    intro h
    have hh := D.localType.involution
    rw [h,orderOf_one] at hh
    omega
  have ha1 : a ≠ 1 := fun h => haE (h ▸ P.E.one_mem)
  obtain ⟨c,hc,he⟩ := P.elementary_sixteen_normalizer_transitive hclass A hA D.z a
    (hEA P.z_mem_E) ha hz1 ha1
  refine ⟨c,hc,he ▸ haE,?_⟩
  intro hcR
  have hcE : c ∈ normalizer (P.E : Set G) :=
    (Geometry.Coordinates.normalizer_E_eq_normalizer_R P).symm ▸ hcR
  exact haE (he ▸ (mem_normalizer_iff.mp hcE D.z).mp P.z_mem_E)

end ReturningPair
end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
