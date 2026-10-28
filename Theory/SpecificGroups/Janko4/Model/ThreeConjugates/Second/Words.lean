module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates

/-!
# Matrix witnesses for the second J₄ involution triple

Untrusted row data for words in `r`, `a*r*a⁻¹`, `b*r*b⁻¹`, where
`r = (a*b*a*b*b)^5`. The product certificates check every multiplication
in the kernel. The invertible matrix T intertwines the original generators
with two such words; no ATLAS generation test is trusted by the proof.

Source matrices: ATLAS J4G1-f2r112B0, as attributed in `Model.Data`.
The word search used the ATLAS J4G1-find1 recipe (Wilson–Nickerson–Bray);
see `source/README.md` for the reproducible witness and proof method.
-/

@[expose] public section
namespace Janko4.ThreeConjugates.SecondCertificate
open GeneratorCertificates

def r : Model := (a * b * a * b * b) ^ 5

def ai : Model := a⁻¹
def bi : Model := b⁻¹
def ar : Model := a * r
def x : Model := ar * ai
def br : Model := b * r
def y : Model := br * bi

def triple : Subgroup Model :=
  Subgroup.zpowers r ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers y

theorem mem_r : r ∈ triple :=
  (le_sup_left.trans le_sup_left : Subgroup.zpowers r ≤ triple)
    (Subgroup.mem_zpowers r)
theorem mem_x : x ∈ triple :=
  (le_sup_right.trans le_sup_left : Subgroup.zpowers x ≤ triple)
    (Subgroup.mem_zpowers x)
theorem mem_y : y ∈ triple :=
  (le_sup_right : Subgroup.zpowers y ≤ triple) (Subgroup.mem_zpowers y)

def u1 : Model := r * y
def u2 : Model := u1 * r
def u3 : Model := u2 * x
def u4 : Model := u3 * r
def u5 : Model := u4 * x
def u6 : Model := u5 * r
def u7 : Model := u6 * x
def u8 : Model := u7 * y
def u9 : Model := u8 * r
def u10 : Model := u9 * y
def u11 : Model := u10 * r
def u12 : Model := u11 * y
def u13 : Model := u12 * x
def u14 : Model := u13 * y
def u15 : Model := u14 * x
def v1 : Model := x * y
def v2 : Model := v1 * r
def v3 : Model := v2 * y
def v4 : Model := v3 * x
def v5 : Model := v4 * y
def v6 : Model := v5 * x
def v7 : Model := v6 * y
def v8 : Model := v7 * r
def v9 : Model := v8 * x
def v10 : Model := v9 * y
def v11 : Model := v10 * r
def v12 : Model := v11 * x
def v13 : Model := v12 * y
def v14 : Model := v13 * r
def v15 : Model := v14 * x
def u2p : Model := u15 * u15
def u4p : Model := u2p * u2p
def u8p : Model := u4p * u4p
def u10p : Model := u8p * u2p
def u11p : Model := u10p * u15
def standardA : Model := u11p * u11p
def vi : Model := v15⁻¹
def vu : Model := v15 * u11p
def standardB : Model := vu * vi

theorem mem_u1 : u1 ∈ triple := triple.mul_mem mem_r mem_y

theorem mem_u2 : u2 ∈ triple := triple.mul_mem mem_u1 mem_r

theorem mem_u3 : u3 ∈ triple := triple.mul_mem mem_u2 mem_x

theorem mem_u4 : u4 ∈ triple := triple.mul_mem mem_u3 mem_r

theorem mem_u5 : u5 ∈ triple := triple.mul_mem mem_u4 mem_x

theorem mem_u6 : u6 ∈ triple := triple.mul_mem mem_u5 mem_r

theorem mem_u7 : u7 ∈ triple := triple.mul_mem mem_u6 mem_x

theorem mem_u8 : u8 ∈ triple := triple.mul_mem mem_u7 mem_y

theorem mem_u9 : u9 ∈ triple := triple.mul_mem mem_u8 mem_r

theorem mem_u10 : u10 ∈ triple := triple.mul_mem mem_u9 mem_y

theorem mem_u11 : u11 ∈ triple := triple.mul_mem mem_u10 mem_r

theorem mem_u12 : u12 ∈ triple := triple.mul_mem mem_u11 mem_y

theorem mem_u13 : u13 ∈ triple := triple.mul_mem mem_u12 mem_x

theorem mem_u14 : u14 ∈ triple := triple.mul_mem mem_u13 mem_y

theorem mem_u15 : u15 ∈ triple := triple.mul_mem mem_u14 mem_x

theorem mem_v1 : v1 ∈ triple := triple.mul_mem mem_x mem_y

theorem mem_v2 : v2 ∈ triple := triple.mul_mem mem_v1 mem_r

theorem mem_v3 : v3 ∈ triple := triple.mul_mem mem_v2 mem_y

theorem mem_v4 : v4 ∈ triple := triple.mul_mem mem_v3 mem_x

theorem mem_v5 : v5 ∈ triple := triple.mul_mem mem_v4 mem_y

theorem mem_v6 : v6 ∈ triple := triple.mul_mem mem_v5 mem_x

theorem mem_v7 : v7 ∈ triple := triple.mul_mem mem_v6 mem_y

theorem mem_v8 : v8 ∈ triple := triple.mul_mem mem_v7 mem_r

theorem mem_v9 : v9 ∈ triple := triple.mul_mem mem_v8 mem_x

theorem mem_v10 : v10 ∈ triple := triple.mul_mem mem_v9 mem_y

theorem mem_v11 : v11 ∈ triple := triple.mul_mem mem_v10 mem_r

theorem mem_v12 : v12 ∈ triple := triple.mul_mem mem_v11 mem_x

theorem mem_v13 : v13 ∈ triple := triple.mul_mem mem_v12 mem_y

theorem mem_v14 : v14 ∈ triple := triple.mul_mem mem_v13 mem_r

theorem mem_v15 : v15 ∈ triple := triple.mul_mem mem_v14 mem_x

theorem mem_u2p : u2p ∈ triple := triple.mul_mem mem_u15 mem_u15

theorem mem_u4p : u4p ∈ triple := triple.mul_mem mem_u2p mem_u2p

theorem mem_u8p : u8p ∈ triple := triple.mul_mem mem_u4p mem_u4p

theorem mem_u10p : u10p ∈ triple := triple.mul_mem mem_u8p mem_u2p

theorem mem_u11p : u11p ∈ triple := triple.mul_mem mem_u10p mem_u15

theorem mem_standardA : standardA ∈ triple := triple.mul_mem mem_u11p mem_u11p

theorem mem_vi : vi ∈ triple := triple.inv_mem mem_v15

theorem mem_vu : vu ∈ triple := triple.mul_mem mem_v15 mem_u11p

theorem mem_standardB : standardB ∈ triple := triple.mul_mem mem_vu mem_vi
end Janko4.ThreeConjugates.SecondCertificate
