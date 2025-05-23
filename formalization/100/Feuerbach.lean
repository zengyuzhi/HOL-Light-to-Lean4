import Mathlib
import Aesop

open Real InnerProductSpace

-- ℝ² as Euclidean space
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

variable {a b c : ℝ²}
variable {r1 r2 : ℝ}
variable {c1 c2 x : ℝ²}
variable {mbc mac mab pbc pac pab ncenter icenter : ℝ²}
variable {nradius iradius : ℝ}
variable {fab fbc fac : ℝ²}
variable {oc : ℝ²}

-- CIRCLES_TANGENT
theorem circles_tangent
    (h1 : 0 ≤ r1) (h2 : 0 ≤ r2)
    (ht : dist c1 c2 = r1 + r2 ∨ dist c1 c2 = |r1 - r2|) :
    (c1 = c2 ∧ r1 = r2) ∨ ∃! x, dist c1 x = r1 ∧ dist c2 x = r2 := by sorry


-- FEUERBACH
theorem feuerbach
    (h_noncollinear : ¬Collinear ℝ ({a, b, c} : Set ℝ²))
    (h_mab : midpoint ℝ a b = mab)
    (h_mbc : midpoint ℝ b c = mbc)
    (h_mac : midpoint ℝ c a = mac)
    (h_nradius1 : dist ncenter mbc = nradius)
    (h_nradius2 : dist ncenter mac = nradius)
    (h_nradius3 : dist ncenter mab = nradius)
    (h_iradius1 : dist icenter pbc = iradius)
    (h_iradius2 : dist icenter pac = iradius)
    (h_iradius3 : dist icenter pab = iradius)
    (h_collinear1 : Collinear ℝ ({a, b, pab} : Set ℝ²))
    (h_orth1 : inner (a - b) (icenter - pab) = (0:ℝ))
    (h_collinear2 : Collinear ℝ ({b, c, pbc} : Set ℝ²))
    (h_orth2 : inner (b - c) (icenter - pbc) = (0:ℝ))
    (h_collinear3 : Collinear ℝ ({a, c, pac} : Set ℝ²))
    (h_orth3 : inner (a - c) (icenter - pac) = (0:ℝ)) :
    ncenter = icenter ∧ nradius = iradius ∨
    ∃! (x : ℝ²), dist ncenter x = nradius ∧ dist icenter x = iradius := by
  have h₁ : 0 ≤ nradius := by
    -- Prove that the radius of the nine-point circle is non-negative.
    have h₁ : 0 ≤ dist ncenter mbc := dist_nonneg
    have h₂ : dist ncenter mbc = nradius := h_nradius1
    linarith
  have h₂ : 0 ≤ iradius := by
    -- Prove that the radius of the incircle is non-negative.
    have h₁ : 0 ≤ dist icenter pbc := dist_nonneg
    have h₂ : dist icenter pbc = iradius := h_iradius1
    linarith
  have h₃ : dist ncenter icenter = nradius + iradius ∨ dist ncenter icenter = |nradius - iradius| := by
    -- Prove that the distance between the centers of the nine-point circle and the incircle is either the sum or the difference of the radii.
    sorry
  -- Apply the circles_tangent theorem to get the desired result.
  have h₄ : (ncenter = icenter ∧ nradius = iradius) ∨ ∃! (x : ℝ²), dist ncenter x = nradius ∧ dist icenter x = iradius := by
    apply circles_tangent h₁ h₂ h₃
  exact h₄



-- NINE_POINT_CIRCLE_1
theorem nine_point_circle_1
    (h_noncollinear : ¬Collinear ℝ ({a, b, c} : Set ℝ²))
    (h_mab : midpoint ℝ a b = mab)
    (h_mbc : midpoint ℝ b c = mbc)
    (h_mac : midpoint ℝ c a = mac)
    (h_nradius1 : dist ncenter mbc = nradius)
    (h_nradius2 : dist ncenter mac = nradius)
    (h_nradius3 : dist ncenter mab = nradius)
    (h_collinear1 : Collinear ℝ ({a, b, fab} : Set ℝ²))
    (h_orth1 : inner (a - b) (c - fab) = (0:ℝ))
    (h_collinear2 : Collinear ℝ ({b, c, fbc} : Set ℝ²))
    (h_orth2 : inner (b - c) (a - fbc) = (0:ℝ))
    (h_collinear3 : Collinear ℝ ({c, a, fac} :  Set ℝ²))
    (h_orth3 : inner (c - a) (b - fac) = (0:ℝ)) :
    dist o fab = nradius ∧ dist o fbc = nradius ∧ dist o fac = nradius := by
  have h₁ : o = ncenter := by sorry
  have h₂ : dist ncenter fab = nradius := by sorry
  have h₃ : dist ncenter fbc = nradius := by sorry
  have h₄ : dist ncenter fac = nradius := by sorry
  have h₅ : dist o fab = nradius := by sorry
  have h₆ : dist o fbc = nradius := by sorry
  have h₇ : dist o fac = nradius := by sorry
  exact ⟨h₅, h₆, h₇⟩

-- NINE_POINT_CIRCLE_2
theorem nine_point_circle_2
    (h_noncollinear : ¬Collinear ℝ ({a, b, c} : Set ℝ²))
    (h_mab : midpoint ℝ a b = mab)
    (h_mbc : midpoint ℝ b c = mbc)
    (h_mac : midpoint ℝ c a = mac)
    (h_nradius1 : dist ncenter mbc = nradius)
    (h_nradius2 : dist ncenter mac = nradius)
    (h_nradius3 : dist ncenter mab = nradius)
    (h_collinear1 : Collinear ℝ ({a, b, fab} : Set ℝ²))
    (h_orth1 : inner (a - b) (c - fab) = (0:ℝ))
    (h_collinear2 : Collinear ℝ ({b, c, fbc} : Set ℝ²))
    (h_orth2 : inner (b - c) (a - fbc) = (0:ℝ))
    (h_collinear3 : Collinear ℝ ({c, a, fac} : Set ℝ²))
    (h_orth3 : inner (c - a) (b - fac) = (0:ℝ))
    (h_oc1 : Collinear ℝ ({oc, a, fbc} : Set ℝ²))
    (h_oc2 : Collinear ℝ ({oc, b, fac} : Set ℝ²))
    (h_oc3 : Collinear ℝ ({oc, c, fab} : Set ℝ²)) :
    dist ncenter (midpoint ℝ oc a) = nradius ∧
    dist ncenter (midpoint ℝ oc b) = nradius ∧
    dist ncenter (midpoint ℝ oc c) = nradius := by sorry
